import VeriTile.Triton.Float.TermModel
import VeriTile.Triton.Float.ValueTransport
import VeriTile.Meta.StatementAudit

/-! Atomic reduction expressions retain storage dtype, previous shared value,
and incoming operand in order. Only the primitive is interpreted here; no
commutation, reduction-tree equivalence or complete-kernel law is supplied. -/
namespace VeriTile.Triton.FP.Equational
open Structural
noncomputable section

/-- Enable only the max/min source operations supported by Structural. -/
def atomicExpressionBackend (M : Algebra (Term α)) : Algebra (Term α) :=
  { M with atomicReduce := fun operation dtype =>
      if operation = .max ∨ operation = .min then
        some (fun previous incoming => .app (.atomicReduce operation dtype) [previous,incoming])
      else none }

/-- A missing primitive remains outside the interpretation theorem below.
The fallback keeps unrelated primitive interpretations unchanged. -/
def atomicCalls {α : Type} [Inhabited α] (M : Algebra α)
    (fallback : Symbol → List α → α) : Symbol → List α → α
  | .atomicReduce operation dtype,[previous,incoming] =>
      match M.atomicReduce operation dtype with
      | some combine => combine previous incoming
      | none => default
  | symbol,args => fallback symbol args

theorem atomic_expression_evaluates {α β : Type} [Inhabited β]
    (M : Algebra β) (fallback : Symbol → List β → β) (leaf : α → β)
    (operation : RMWOp) (dtype : FloatDType) (previous incoming : Term α)
    (combine : β → β → β) (available : M.atomicReduce operation dtype = some combine) :
    (Term.app (.atomicReduce operation dtype) [previous,incoming]).evaluate leaf (atomicCalls M fallback) =
      combine (previous.evaluate leaf (atomicCalls M fallback))
        (incoming.evaluate leaf (atomicCalls M fallback)) := by
  simp [Term.evaluate,atomicCalls,available]

/-- The expression interpreter preserves an explicitly ordered update fold.
The initial shared value participates; it is never replaced by a reduction seed. -/
theorem atomic_fold_evaluates {α β : Type} [Inhabited β]
    (M : Algebra β) (fallback : Symbol → List β → β) (leaf : α → β)
    (operation : RMWOp) (dtype : FloatDType) (incoming : List (Term α))
    (combine : β → β → β) (available : M.atomicReduce operation dtype = some combine)
    (previous : Term α) :
    (incoming.foldl (fun old value => .app (.atomicReduce operation dtype) [old,value]) previous).evaluate
        leaf (atomicCalls M fallback) =
      (incoming.map (Term.evaluate leaf (atomicCalls M fallback))).foldl combine
        (previous.evaluate leaf (atomicCalls M fallback)) := by
  induction incoming generalizing previous with
  | nil => rfl
  | cons value rest ih =>
      simp only [List.foldl_cons,List.map_cons]
      rw [ih,atomic_expression_evaluates M fallback leaf operation dtype previous value combine available]

#axiomsClean atomic_expression_evaluates
#axiomsClean atomic_fold_evaluates
end
end VeriTile.Triton.FP.Equational
