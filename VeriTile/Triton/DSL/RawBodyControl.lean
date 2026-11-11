import VeriTile.Triton.DSL.SourceDType
namespace VeriTile.Triton.DSL.RawBodyControl
open Lean
syntax "tl.full(" "(" tritonExpr,* ")" ", " tritonExpr ", " tritonDType ")" : tritonExpr
syntax "while " tritonExpr " { " tritonStmt* " }" : tritonStmt
syntax "tl.reshape(" tritonExpr ", " "(" tritonExpr,* ")" ")" : tritonExpr
syntax "tl.permute(" tritonExpr ", " "(" num,* ")" ")" : tritonExpr
syntax (name := splitTupleAssignment) ident "," ident "=" "tl.split(" ident ")" : tritonStmt
syntax (name := independentTupleAssignment) ident "," ident,+ "=" "(" tritonExpr,+,? ")" : tritonStmt

private partial def identifiers (raw : Syntax) : List Name :=
  if raw.isIdent then [raw.getId.eraseMacroScopes]
  else raw.getArgs.toList.flatMap identifiers

mutual
  /-- Bounded simultaneous assignment: every RHS is independent of all target
  registers. Their source order is retained. Dependent swaps are rejected,
  rather than silently changed into sequential assignments. -/
  partial def expandAssignment (raw : Syntax) : MacroM (Array Syntax) := do
    if raw.isOfKind ``splitTupleAssignment then
      let `(tritonStmt| $left:ident, $right:ident = tl.split($source:ident)) := raw
        | Macro.throwErrorAt raw "invalid split assignment"
      let names := [left.getId.eraseMacroScopes,right.getId.eraseMacroScopes]
      unless names.eraseDups.length == 2 do
        Macro.throwErrorAt raw "split assignment requires distinct targets"
      if names.contains source.getId.eraseMacroScopes then
        Macro.throwErrorAt raw "split assignment cannot overwrite its source register"
      return #[
        (← `(tritonStmt| $left:ident = tl.split($source:ident, 0))).raw,
        (← `(tritonStmt| $right:ident = tl.split($source:ident, 1))).raw]
    else if raw.isOfKind ``independentTupleAssignment then
      let targets := #[raw[0]] ++ raw[2].getSepArgs
      let values := raw[5].getSepArgs
      unless targets.size == values.size do
        Macro.throwErrorAt raw "tuple assignment target/value counts differ"
      let names := targets.toList.map (·.getId.eraseMacroScopes)
      unless names.eraseDups.length == names.length do
        Macro.throwErrorAt raw "tuple assignment requires distinct targets"
      for value in values do
        if (identifiers value).any (fun read => names.any (·.isPrefixOf read)) then
          Macro.throwErrorAt raw "dependent tuple assignment is unsupported"
      (targets.zip values).mapM fun (target,value) => do
        let target : Ident := ⟨target⟩
        let value : TSyntax `tritonExpr := ⟨value⟩
        return (← `(tritonStmt| $target:ident = $value:tritonExpr)).raw
    else return #[← expandNested raw]

  /-- Only statement sequences may expand. Expression operands and their
  ordering remain untouched, including inside nested range/branch bodies. -/
  partial def expandNested (raw : Syntax) : MacroM Syntax := do
    if raw.isOfKind nullKind then
      let groups ← raw.getArgs.mapM expandAssignment
      return raw.setArgs groups.flatten
    else return raw.setArgs (← raw.getArgs.mapM expandNested)
end

def expandAssignments (body : Array (TSyntax `tritonStmt)) : MacroM (Array (TSyntax `tritonStmt)) := do
  let groups ← body.mapM (fun stmt => expandAssignment stmt.raw)
  return groups.flatten.map (fun raw => ⟨raw⟩)

/-- Source writes, including nested statements and loop bindings. -/
private partial def writes (raw : Syntax) : List Name := Id.run do
  let args := raw.getArgs.toList
  let operators := ["=",":=","+=","-=","*=","/="]
  let assignment := args.findIdx? (fun arg => arg.isAtom && operators.contains arg.getAtomVal.trimAscii.toString)
  let direct := match assignment with
    | some n => (args.take n).flatMap identifiers
    | none => []
  let binder := match args with
    | first :: counter :: _ =>
      if first.isAtom && ["for","tl.for"].contains first.getAtomVal.trimAscii.toString && counter.isIdent
      then [counter.getId.eraseMacroScopes] else []
    | _ => []
  return direct ++ binder ++ args.flatMap writes

partial def normalize (raw : Syntax) : MacroM Syntax := do
  let raw := raw.setArgs (← raw.getArgs.mapM normalize)
  match raw with
  | `(tritonExpr| tl.reshape($value:tritonExpr, ($dims:tritonExpr,*))) =>
    return (← `(tritonExpr| tl.reshape($value:tritonExpr, [$dims,*]))).raw
  | `(tritonExpr| tl.permute($value:tritonExpr, ($axes:num,*))) =>
    return (← `(tritonExpr| tl.permute($value:tritonExpr, [$axes,*]))).raw
  | `(tritonExpr| tl.full(($dims:tritonExpr,*), $value:tritonExpr, $dtype:tritonDType)) =>
    let value ← if ["tl.uint8","tl.uint16","tl.uint32","tl.uint64"].contains
        (dtype.raw.reprint.getD "").trimAscii.toString then
      let value ← match value with
        | `(tritonExpr| $n:num) => do
          let term : TSyntax `term := ⟨n.raw⟩
          let typed ← `(term| ($term : Nat))
          `(tritonExpr| $($typed))
        | _ => pure value
      `(tritonExpr| tl.cast($value:tritonExpr, $dtype:tritonDType))
      else pure value
    let keyword := mkIdent (Name.mkSimple "dtype")
    return (← `(tritonExpr| tl.full([$dims,*], $value, $keyword:ident=$dtype:tritonDType))).raw
  | `(tritonStmt| while $condition:tritonExpr { $body:tritonStmt* }) => do
    let `(tritonExpr| $counter:ident < $bound:ident) := condition
      | Macro.throwErrorAt condition "affine while requires a scalar counter < unchanged bound"
    let some last := body[body.size-1]?
      | Macro.throwErrorAt raw "affine while requires a final counter increment"
    let `(tritonStmt| $updated:ident += $stride:tritonExpr) := last
      | Macro.throwErrorAt last "affine while requires a final counter += step"
    unless updated.getId.eraseMacroScopes == counter.getId.eraseMacroScopes do
      Macro.throwErrorAt last "affine while must update its own counter"
    let inner := (body.toList.take (body.size-1)).flatMap (fun stmt => writes stmt.raw)
    if inner.contains counter.getId.eraseMacroScopes then
      Macro.throwErrorAt raw "affine while counter may only be written by the final increment"
    let protectedNames := bound.getId.eraseMacroScopes :: identifiers stride.raw
    let allWrites := body.toList.flatMap (fun stmt => writes stmt.raw)
    if protectedNames.any allWrites.contains then
      Macro.throwErrorAt raw "affine while bound and stride must remain unchanged"
    let typedStride ← match stride with
      | `(tritonExpr| $name:ident) => do
        let term ← `(term| ($name:ident : Nat))
        `(tritonExpr| $($term))
      | `(tritonExpr| $n:num) => do
        let term : TSyntax `term := ⟨n.raw⟩
        `(tritonExpr| $($term))
      | _ => Macro.throwErrorAt stride "affine while requires a Nat constexpr step"
    let update ← `(tritonStmt| $counter:ident += $typedStride:tritonExpr)
    let emitted := body.set! (body.size-1) update
    return (← `(tritonStmt| for $counter:ident in range($counter:ident, $bound:ident, $typedStride:tritonExpr) { $emitted* })).raw
  | _ => return raw

end VeriTile.Triton.DSL.RawBodyControl
