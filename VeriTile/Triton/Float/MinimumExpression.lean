import VeriTile.Triton.Float.TermModel
import VeriTile.Meta.StatementAudit

/-! Optional floating minimum calls retain their own label and exact precision.
No identity with negated maximum, or NaN/signed-zero law, is introduced. -/
namespace VeriTile.Triton.FP.Equational
open Structural
noncomputable section

def withMinimumCalls {α : Type} (base : Algebra (Term α)) : Algebra (Term α) :=
  { base with
    minimum := fun precision dtype =>
      some (fun a b => .app (.minimum precision dtype) [a,b]) }

def minimumCalls {α : Type} (M : Algebra α) (fallback : Symbol → List α → α) : Symbol → List α → α
  | .minimum precision dtype,[a,b] => match M.minimum precision dtype with
    | some minimum => minimum a b
    | none => fallback (.minimum precision dtype) [a,b]
  | op,args => fallback op args

theorem minimum_evaluates {α β : Type} (M : Algebra β) (fallback : Symbol → List β → β)
    (leaf : α → β) (precision : Option ComputeDType) (dtype : FloatDType)
    (a b : Term α) (minimum : β → β → β) (available : M.minimum precision dtype = some minimum) :
    (Term.app (.minimum precision dtype) [a,b]).evaluate leaf (minimumCalls M fallback) =
      minimum (a.evaluate leaf (minimumCalls M fallback)) (b.evaluate leaf (minimumCalls M fallback)) := by
  simp only [Term.evaluate,List.map_cons,List.map_nil,minimumCalls,available]

theorem withMinimumCalls_supported {α : Type} (base : Algebra (Term α))
    (precision : Option ComputeDType) (dtype : FloatDType) :
    (withMinimumCalls base).minimum precision dtype =
      some (fun a b => .app (.minimum precision dtype) [a,b]) := rfl

#axiomsClean minimum_evaluates
#axiomsClean withMinimumCalls_supported
end
end VeriTile.Triton.FP.Equational
