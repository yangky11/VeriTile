import VeriTile.Triton.Float.Equational
import VeriTile.Meta.StatementAudit

/-! An explicit compiler-contraction relation, not floating-point equality.
Only an FP32 multiply directly consumed by an FP32 add can contract. Casts,
other precisions, dot calls and operand order inside the product are retained.
Different store uses may carry different derivations. Interpreting the target
with word arithmetic specifies those choices without asserting that strict
source evaluation produces identical words. -/
namespace VeriTile.Triton.FP.Equational

variable {α : Type}

def Term.mul32 (a b : Term α) : Term α :=
  .app (.binary (some .fp32) .real .mul) [a,b]

def Term.fma32 (a b c : Term α) : Term α := .app (.fma .fp32) [a,b,c]

inductive FmaContraction : Term α → Term α → Prop where
  | refl (a) : FmaContraction a a
  | trans {a b c} : FmaContraction a b → FmaContraction b c → FmaContraction a c
  | context (op : Symbol) (before after : List (Term α)) {a b} :
      FmaContraction a b → FmaContraction (.app op (before ++ a :: after))
        (.app op (before ++ b :: after))
  | left (a b c : Term α) : FmaContraction ((a.mul32 b).add c) (a.fma32 b c)
  | right (a b c : Term α) : FmaContraction (c.add (a.mul32 b)) (a.fma32 b c)

inductive FmaSide where
  | left | right
  deriving DecidableEq

/-- A checked local rewrite. It cannot cross a cast, change a precision, swap
product operands, or remove a term. The two possible choices remain explicit. -/
def contractRoot (side : FmaSide) (source : Term α) : Option (Term α) :=
  match side, source with
  | .left, .app (.binary (some .fp32) .real .add)
      [.app (.binary (some .fp32) .real .mul) [a,b], c] => some (a.fma32 b c)
  | .right, .app (.binary (some .fp32) .real .add)
      [c, .app (.binary (some .fp32) .real .mul) [a,b]] => some (a.fma32 b c)
  | _, _ => none

theorem contractRoot_sound (side : FmaSide) (source target : Term α)
    (accepted : contractRoot side source = some target) : FmaContraction source target := by
  unfold contractRoot at accepted
  split at accepted
  · cases accepted
    exact .left _ _ _
  · cases accepted
    exact .right _ _ _
  · cases accepted

/-- Operand positions are finite metadata supplied by a compiler witness. -/
def contractAt (side : FmaSide) : List Nat → Term α → Option (Term α)
  | [], source => contractRoot side source
  | index :: rest, .app op args =>
    if h : index < args.length then
      (contractAt side rest args[index]).map fun target => .app op (args.set index target)
    else none
  | _ :: _, .leaf _ => none

theorem contractAt_sound (side : FmaSide) (path : List Nat) (source target : Term α)
    (accepted : contractAt side path source = some target) : FmaContraction source target := by
  induction path generalizing source target with
  | nil => exact contractRoot_sound side source target accepted
  | cons index rest ih =>
    cases source with
    | leaf value => simp [contractAt] at accepted
    | app op args =>
      simp only [contractAt] at accepted
      split at accepted
      · rename_i inside
        cases result : contractAt side rest args[index] with
        | none => simp [result] at accepted
        | some changed =>
          simp only [result,Option.map_some,Option.some.injEq] at accepted
          subst target
          rw [List.set_eq_take_append_cons_drop,ite_eq_left inside]
          have step := FmaContraction.context op (args.take index) (args.drop (index+1))
            (ih _ _ result)
          simpa only [List.getElem_cons_drop inside,List.take_append_drop] using step
      · cases accepted

structure FmaEdit where
  path : List Nat
  side : FmaSide

def contractAll : List FmaEdit → Term α → Option (Term α)
  | [], source => some source
  | edit :: rest, source => do
    let changed ← contractAt edit.side edit.path source
    contractAll rest changed

theorem contractAll_sound (edits : List FmaEdit) (source target : Term α)
    (accepted : contractAll edits source = some target) : FmaContraction source target := by
  induction edits generalizing source with
  | nil => cases accepted; exact .refl _
  | cons edit rest ih =>
    simp only [contractAll] at accepted
    cases result : contractAt edit.side edit.path source with
    | none => simp [result] at accepted
    | some changed =>
      simp only [result] at accepted
      exact .trans (contractAt_sound _ _ _ _ result) (ih changed accepted)

/-- Numerical leaves supplied by the caller retain their multiplicities. This
is a structural invariant, not an error bound or a statement about NaN results. -/
def Term.inputs : Term α → List α
  | .leaf a => [a]
  | .app _ args => args.flatMap Term.inputs

theorem FmaContraction.inputs_perm {source target : Term α} (h : FmaContraction source target) :
    source.inputs.Perm target.inputs := by
  induction h with
  | refl => exact .refl _
  | trans _ _ first second => exact first.trans second
  | context op before after _ ih =>
    simpa only [Term.inputs,List.flatMap_append,List.flatMap_cons] using
      List.Perm.append_left (before.flatMap Term.inputs) (ih.append_right (after.flatMap Term.inputs))
  | left a b c => simp [Term.inputs,Term.add,Term.mul32,Term.fma32,List.append_assoc]
  | right a b c =>
    simp only [Term.inputs,Term.add,Term.mul32,Term.fma32,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    simpa only [List.append_assoc] using List.perm_append_comm (l₁ := c.inputs) (l₂ := a.inputs ++ b.inputs)

#axiomsClean contractRoot_sound
#axiomsClean contractAt_sound
#axiomsClean contractAll_sound
#axiomsClean FmaContraction.inputs_perm
end VeriTile.Triton.FP.Equational
