import VeriTile.Triton.Float.ComparisonInterpretation
import tests.lean.InductorExtrema

/-! Comparisons use numerical interpretations rather than symbolic identity.
Missing callbacks fail even on empty tiles. These are model/transport checks;
they make no native IEEE claim about the illustrative Nat carrier. -/
namespace VeriTile.Tests.ComparisonInterpretation
open VeriTile.Triton FP.Structural
set_option backward.isDefEq.respectTransparency false
noncomputable section

abbrev Tagged := Nat × Nat

def numeric (rest : Algebra Nat) : Algebra Nat :=
  { rest with
    compareLt := fun _ _ => some (fun a b => decide (a < b))
    compareLe := fun _ _ => some (fun a b => decide (a ≤ b))
    compareEq := fun _ _ => some (fun a b => decide (a = b)) }

def values (s : State Tagged) : State Tagged :=
  (s.setReg "a" .real [] (fun _ => (7,0))).setReg "b" .real [] (fun _ => (7,1))

/-- Distinct symbolic tags denote equal numerical values, so the actual helper
expression selects the right operand, preserving that operand's full payload. -/
theorem equal_numbers_choose_right (base : Algebra Tagged) (rest : Algebra Nat) (s : State Tagged) :
    evalExpr (base.withInterpretedComparisons (numeric rest) Prod.fst)
      InductorExtrema.selectedExpression (values s) = some (fun _ => (7,1)) := by
  simp [InductorExtrema.selectedExpression,evalExpr,evalComputeOp_alg,evalOp_unfold,
    numericLt,numericEq,Algebra.withInterpretedComparisons,numeric,values,State.setReg,
    ComputeDType.eraseDType,bop]

/-- A nonreflexive equality policy is preserved. The adapter must not replace
self-comparison by reflexivity of the symbolic data structure. -/
theorem nonreflexive_equality_retains_left (base : Algebra Tagged) (rest : Algebra Nat) (s : State Tagged) :
    evalExpr (base.withInterpretedComparisons
      { numeric rest with compareEq := fun _ _ => some (fun _ _ => Bool.false) } Prod.fst)
      InductorExtrema.selectedExpression (values s) = some (fun _ => (7,0)) := by
  simp [InductorExtrema.selectedExpression,evalExpr,evalComputeOp_alg,evalOp_unfold,
    numericLt,numericEq,Algebra.withInterpretedComparisons,numeric,values,State.setReg,
    ComputeDType.eraseDType,bop]

theorem missing_equality_empty {α β : Type} [Inhabited α]
    (base : Algebra α) (target : Algebra β) (interpret : α → β)
    (p : Option ComputeDType) (s : State α) (a b : Op .real [0])
    (missing : target.compareEq p .real = none) :
    evalOp (base.withInterpretedComparisons target interpret) p
      (.ne .real (.consSame .nil) a b) s = none := by
  rw [evalOp_unfold]
  simp [numericEq,Algebra.withInterpretedComparisons,missing]

theorem missing_order_empty {α β : Type} [Inhabited α]
    (base : Algebra α) (target : Algebra β) (interpret : α → β)
    (p : Option ComputeDType) (s : State α) (a b : Op .real [0])
    (missing : target.compareLt p .real = none) :
    evalOp (base.withInterpretedComparisons target interpret) p
      (.gt .real (.consSame .nil) a b) s = none := by
  rw [evalOp_unfold]
  simp [numericLt,Algebra.withInterpretedComparisons,missing]

theorem missing_le_empty {α β : Type} [Inhabited α]
    (base : Algebra α) (target : Algebra β) (interpret : α → β)
    (p : Option ComputeDType) (s : State α) (a b : Op .real [0])
    (missing : target.compareLe p .real = none) :
    evalOp (base.withInterpretedComparisons target interpret) p
      (.ge .real (.consSame .nil) a b) s = none := by
  rw [evalOp_unfold]
  simp [numericLe,Algebra.withInterpretedComparisons,missing]

#axiomsClean equal_numbers_choose_right
#axiomsClean nonreflexive_equality_retains_left
#axiomsClean missing_equality_empty
#axiomsClean missing_order_empty
#axiomsClean missing_le_empty
end
end VeriTile.Tests.ComparisonInterpretation
