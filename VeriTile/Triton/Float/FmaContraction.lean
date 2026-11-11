import VeriTile.Triton.Float.Equational
import VeriTile.Meta.StatementAudit

/-! An explicit compiler-contraction relation, not floating-point equality.
An FP32 multiply directly consumed by an FP32 add, or explicitly
selected subtraction, can contract. Untagged real-channel operations require
a separate opt-in declaring FP32 native contraction; their source tags stay
untouched. This declaration is not inferred from the real dtype. Casts,
other precisions, dot calls and operand order inside the product are retained.
Different store uses may carry different derivations. Interpreting the target
with word arithmetic specifies those choices without asserting that strict
source evaluation produces identical words. -/
namespace VeriTile.Triton.FP.Equational

variable {α : Type}

def Term.mul32 (a b : Term α) : Term α :=
  .app (.binary (some .fp32) .real .mul) [a,b]

def Term.sub32 (a b : Term α) : Term α :=
  .app (.binary (some .fp32) .real .sub) [a,b]

def Term.neg32 (a : Term α) : Term α :=
  .app (.unary (some .fp32) (.neg .real)) [a]

/-- Untagged source arithmetic. These helpers do not assign it a precision. -/
def Term.mulUnscoped (a b : Term α) : Term α :=
  .app (.binary none .real .mul) [a,b]

def Term.addUnscoped (a b : Term α) : Term α :=
  .app (.binary none .real .add) [a,b]

def Term.subUnscoped (a b : Term α) : Term α :=
  .app (.binary none .real .sub) [a,b]

def Term.fma32 (a b c : Term α) : Term α := .app (.fma .fp32) [a,b,c]

inductive FmaContraction : Term α → Term α → Prop where
  | refl (a) : FmaContraction a a
  | trans {a b c} : FmaContraction a b → FmaContraction b c → FmaContraction a c
  | context (op : Symbol) (before after : List (Term α)) {a b} :
      FmaContraction a b → FmaContraction (.app op (before ++ a :: after))
        (.app op (before ++ b :: after))
  | left (a b c : Term α) : FmaContraction ((a.mul32 b).add c) (a.fma32 b c)
  | right (a b c : Term α) : FmaContraction (c.add (a.mul32 b)) (a.fma32 b c)

  | subtractLeft (a b c : Term α) :
      FmaContraction ((a.mul32 b).sub32 c) (a.fma32 b c.neg32)
  | subtractRight (a b c : Term α) :
      FmaContraction (c.sub32 (a.mul32 b)) (a.neg32.fma32 b c)

  /-- The consumer must declare the native FP32 interpretation of these
  untagged operations. These constructors assert no numerical equality. -/
  | unscopedLeft32 (a b c : Term α) :
      FmaContraction ((a.mulUnscoped b).addUnscoped c) (a.fma32 b c)
  | unscopedRight32 (a b c : Term α) :
      FmaContraction (c.addUnscoped (a.mulUnscoped b)) (a.fma32 b c)
  | unscopedSubtractLeft32 (a b c : Term α) :
      FmaContraction ((a.mulUnscoped b).subUnscoped c) (a.fma32 b c.neg32)
  | unscopedSubtractRight32 (a b c : Term α) :
      FmaContraction (c.subUnscoped (a.mulUnscoped b)) (a.neg32.fma32 b c)

/-- Subtraction must be opted into by the edit witness. Existing addition
choices do not accept subtraction or gain new alternatives. Untagged sources
require an explicit FP32 native-policy choice; tagged and untagged operations
are never mixed by the checker. -/
inductive FmaCombine where
  | add | subtract | addUnscoped32 | subtractUnscoped32
  deriving DecidableEq

inductive FmaSide where
  | left | right
  deriving DecidableEq

/-- A checked local rewrite. It cannot cross a cast, change an explicit source
precision, swap product operands, or remove a term. Untagged-to-FP32 contraction
requires its own declared mode. The choices remain explicit. -/
def contractRoot (side : FmaSide) (source : Term α)
    (combine : FmaCombine := .add) : Option (Term α) :=
  match combine, side, source with
  | .add, .left, .app (.binary (some .fp32) .real .add)
      [.app (.binary (some .fp32) .real .mul) [a,b], c] => some (a.fma32 b c)
  | .add, .right, .app (.binary (some .fp32) .real .add)
      [c, .app (.binary (some .fp32) .real .mul) [a,b]] => some (a.fma32 b c)
  | .subtract, .left, .app (.binary (some .fp32) .real .sub)
      [.app (.binary (some .fp32) .real .mul) [a,b], c] => some (a.fma32 b c.neg32)
  | .subtract, .right, .app (.binary (some .fp32) .real .sub)
      [c, .app (.binary (some .fp32) .real .mul) [a,b]] => some (a.neg32.fma32 b c)
  | .addUnscoped32, .left, .app (.binary none .real .add)
      [.app (.binary none .real .mul) [a,b], c] => some (a.fma32 b c)
  | .addUnscoped32, .right, .app (.binary none .real .add)
      [c, .app (.binary none .real .mul) [a,b]] => some (a.fma32 b c)
  | .subtractUnscoped32, .left, .app (.binary none .real .sub)
      [.app (.binary none .real .mul) [a,b], c] => some (a.fma32 b c.neg32)
  | .subtractUnscoped32, .right, .app (.binary none .real .sub)
      [c, .app (.binary none .real .mul) [a,b]] => some (a.neg32.fma32 b c)
  | _, _, _ => none

theorem contractRoot_sound (side : FmaSide) (source target : Term α)
    (combine : FmaCombine) (accepted : contractRoot side source combine = some target) : FmaContraction source target := by
  unfold contractRoot at accepted
  split at accepted
  · cases accepted
    exact .left _ _ _
  · cases accepted
    exact .right _ _ _
  · cases accepted
    exact .subtractLeft _ _ _
  · cases accepted
    exact .subtractRight _ _ _
  · cases accepted
    exact .unscopedLeft32 _ _ _
  · cases accepted
    exact .unscopedRight32 _ _ _
  · cases accepted
    exact .unscopedSubtractLeft32 _ _ _
  · cases accepted
    exact .unscopedSubtractRight32 _ _ _
  · cases accepted

/-- Operand positions are finite metadata supplied by a compiler witness. -/
def contractAt (side : FmaSide) (path : List Nat) (source : Term α)
    (combine : FmaCombine := .add) : Option (Term α) :=
  match path, source with
  | [], source => contractRoot side source combine
  | index :: rest, .app op args =>
    if h : index < args.length then
      (contractAt side rest args[index] combine).map fun target => .app op (args.set index target)
    else none
  | _ :: _, .leaf _ => none

theorem contractAt_sound (side : FmaSide) (path : List Nat) (source target : Term α)
    (combine : FmaCombine) (accepted : contractAt side path source combine = some target) : FmaContraction source target := by
  induction path generalizing source target with
  | nil => exact contractRoot_sound side source target combine accepted
  | cons index rest ih =>
    cases source with
    | leaf value => simp [contractAt] at accepted
    | app op args =>
      simp only [contractAt] at accepted
      split at accepted
      · rename_i inside
        cases result : contractAt side rest args[index] combine with
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
  combine : FmaCombine := .add

def contractAll : List FmaEdit → Term α → Option (Term α)
  | [], source => some source
  | edit :: rest, source => do
    let changed ← contractAt edit.side edit.path source edit.combine
    contractAll rest changed

theorem contractAll_sound (edits : List FmaEdit) (source target : Term α)
    (accepted : contractAll edits source = some target) : FmaContraction source target := by
  induction edits generalizing source with
  | nil => cases accepted; exact .refl _
  | cons edit rest ih =>
    simp only [contractAll] at accepted
    cases result : contractAt edit.side edit.path source edit.combine with
    | none => simp [result] at accepted
    | some changed =>
      simp only [result] at accepted
      exact .trans (contractAt_sound _ _ _ _ _ result) (ih changed accepted)

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

  | subtractLeft a b c =>
    simp [Term.inputs,Term.sub32,Term.neg32,Term.mul32,Term.fma32,List.append_assoc]
  | subtractRight a b c =>
    simp only [Term.inputs,Term.sub32,Term.neg32,Term.mul32,Term.fma32,
      List.flatMap_cons,List.flatMap_nil,List.append_nil]
    simpa only [List.append_assoc] using List.perm_append_comm (l₁ := c.inputs) (l₂ := a.inputs ++ b.inputs)

  | unscopedLeft32 a b c =>
    simp [Term.inputs,Term.addUnscoped,Term.mulUnscoped,Term.fma32,List.append_assoc]
  | unscopedRight32 a b c =>
    simp only [Term.inputs,Term.addUnscoped,Term.mulUnscoped,Term.fma32,
      List.flatMap_cons,List.flatMap_nil,List.append_nil]
    simpa only [List.append_assoc] using List.perm_append_comm (l₁ := c.inputs) (l₂ := a.inputs ++ b.inputs)
  | unscopedSubtractLeft32 a b c =>
    simp [Term.inputs,Term.subUnscoped,Term.neg32,Term.mulUnscoped,Term.fma32,List.append_assoc]
  | unscopedSubtractRight32 a b c =>
    simp only [Term.inputs,Term.subUnscoped,Term.neg32,Term.mulUnscoped,Term.fma32,
      List.flatMap_cons,List.flatMap_nil,List.append_nil]
    simpa only [List.append_assoc] using List.perm_append_comm (l₁ := c.inputs) (l₂ := a.inputs ++ b.inputs)

#axiomsClean contractRoot_sound
#axiomsClean contractAt_sound
#axiomsClean contractAll_sound
#axiomsClean FmaContraction.inputs_perm
end VeriTile.Triton.FP.Equational
