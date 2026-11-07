import Lean
import VeriTile.Triton.DSL.Syntax
import VeriTile.Triton.Core.Types

/-! Explicit interpretation of literals in pasted Python source. The default
DSL retains exact mathematical decimal literals. `pythonFloat32` instead
selects Python binary64 parsing followed by binary32 conversion, and emits the
exact rational value of that finite constant. This frontend conversion is not
a floating-point execution theorem. Runtime operations are unchanged.

This policy interprets individual literals. A source adapter must separately
reject or model Python/constexpr scalar arithmetic before tensor promotion:
rounding each literal does not model Python evaluation of `0.1 + 0.2` or `1 / 13`.
That admission check must also follow scalar aliases and nested expressions.
Host integer expression results promoted to floating tensors must likewise be
checked under the frozen constexpr configuration; exact integer index arithmetic
does not itself imply exact float32 scalar promotion.
Bare integers not exactly representable in binary32 are conservatively rejected
here until context-dependent integer promotion is modeled. -/
namespace VeriTile.Triton

inductive LiteralPolicy where
  | exactDecimal
  | pythonFloat32
  deriving DecidableEq

/-- Meanings of externally resolved, unary source helper names. The caller
must establish the corresponding Python import; spelling alone is insufficient. -/
inductive SourceHelper where
  | rsqrt

namespace DSL.SourceLiterals
open Lean

/-- Exact magnitude of a finite binary32 word. Signed zero denotes real zero. -/
def binary32Rational (bits : UInt32) : Option Rat := do
  let bits : Nat := bits.toNat
  let exponent : Nat := bits / 2^23 % 256
  let fraction : Nat := bits % 2^23
  if exponent == 255 then none else do
    let mantissa : Nat := if exponent == 0 then fraction else 2^23 + fraction
    let power : Int := if exponent == 0 then -149 else (exponent : Int) - 150
    let magnitude : Rat := if power < 0 then (mantissa : Rat) / (2 ^ power.natAbs : Nat)
      else (mantissa * 2 ^ power.toNat : Nat)
    return if bits / 2^31 == 0 then magnitude else -magnitude

/-- The source adapter's finite Python-scalar interpretation. Both conversions
run in the frontend; the emitted Lean term contains only the resulting rational. -/
def scientificFloat32 (mantissa : Nat) (negativeExponent : Bool) (exponent : Nat) : Option Rat :=
  binary32Rational (Float.ofScientific mantissa negativeExponent exponent).toFloat32.toBits

private def rationalTerm (value : Rat) : MacroM (TSyntax `term) := do
  let numerator := Syntax.mkNumLit (toString value.num.natAbs)
  let denominator := Syntax.mkNumLit (toString value.den)
  let magnitude ← `(term| ($numerator:num : ℝ) / ($denominator:num : ℝ))
  if value.num < 0 then `(term| -$magnitude) else pure magnitude

partial def lower (policy : LiteralPolicy) (helpers : List (String × SourceHelper))
    (raw : Syntax) : MacroM Syntax := do
  if policy == .pythonFloat32 then
    let name := if raw.isAtom then raw.getAtomVal else if raw.isIdent then raw.getId.eraseMacroScopes.toString else ""
    if ["tl.float64", "tl.float16", "tl.bfloat16", "tl.float8e4nv", "tl.float8e5"].contains name then
      Macro.throwErrorAt raw "pythonFloat32 literals do not support non-FP32 floating conversions"
  if let `(tritonStmt| $name:ident = $_:tritonExpr) := raw then
    let name := name.getId.eraseMacroScopes.toString
    if helpers.any (fun binding => binding.1 == name || binding.1.startsWith (name ++ ".")) then
      Macro.throwErrorAt raw "assignment shadows a source helper binding"
  let raw := raw.setArgs (← raw.getArgs.mapM (lower policy helpers))
  match raw with
  | `(tritonExpr| $n:num) =>
    if policy == .exactDecimal then return raw
    -- Bare Python integers are promoted according to their expression's dtype.
    -- Until that context is tracked here, accept only values whose integer and
    -- binary32 interpretations coincide. Keep their integer syntax for indices.
    let value := n.getNat
    unless scientificFloat32 value Bool.false 0 == some (value : Rat) do
      Macro.throwErrorAt raw "integer literal is not exactly representable in float32; context-dependent scalar promotion is unsupported"
    return raw
  | `(tritonExpr| $n:scientific) =>
    if policy == .exactDecimal then return raw
    let (mantissa, sign, exponent) := n.getScientific
    let some value := scientificFloat32 mantissa sign exponent
      | Macro.throwErrorAt raw "Python floating literal is nonfinite after float32 conversion"
    let value ← rationalTerm value
    return (← `(tritonExpr| $(($value:term : ℝ)))).raw
  | `(tritonExpr| $helper:ident($value:tritonExpr)) =>
    match helpers.lookup helper.getId.eraseMacroScopes.toString with
    | some .rsqrt => return (← `(tritonExpr| tl.rsqrt($value:tritonExpr))).raw
    | none => return raw
  | _ => return raw

end DSL.SourceLiterals
end VeriTile.Triton
