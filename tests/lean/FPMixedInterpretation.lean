import VeriTile.Triton.Float.MixedInterpretation

/-! Nested primitive families use one interpreter while preserving the two
reduction operands and the atomic seed's left-argument position. -/
namespace FPMixedInterpretationTests
open VeriTile.Triton FP.Structural FP.Equational
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

def nested (seed a b x y : Term α) : Term α :=
  .app (.atomicReduce .max .fp32) [seed,
    .app (.minimum (some .fp32) .real)
      [mixedSymbolic.reduceMax (some .fp32) (shape := [2]) ⟨0,by decide⟩ Bool.false
        (fun i => if i.1.val = 0 then a else b) (),
       .app (.binary none .bf16 .mul) [x,y]]]

theorem nested_preserves_arguments (M : Algebra α) (D : DotAccumulator α)
    (fallback : Symbol → List α → α) (minimum combine : α → α → α)
    (minAvailable : M.minimum (some .fp32) .real = some minimum)
    (atomicAvailable : M.atomicReduce .max .fp32 = some combine)
    (seed a b x y : α) :
    (nested (.leaf seed) (.leaf a) (.leaf b) (.leaf x) (.leaf y)).evaluate id (mixedCalls M D fallback) =
      combine seed (minimum
        (M.reduceMax (some .fp32) (shape := [2]) ⟨0,by decide⟩ Bool.false (fun i => if i.1.val = 0 then a else b) ())
        (M.binary none .bf16 .mul x y)) := by
  rw [nested,mixed_atomic_evaluates M D fallback id .max .fp32 _ _ combine atomicAvailable,
    mixed_minimum_evaluates M D fallback id (some .fp32) .real _ _ minimum minAvailable,
    mixed_maximum_evaluates]
  simp only [Term.evaluate,List.map_cons,List.map_nil,id_eq,mixedCalls,primitiveCalls,dotCalls,scalarCalls]
  congr 3
  funext i
  split <;> simp only [Term.evaluate,id_eq]

#axiomsClean nested_preserves_arguments
end
end FPMixedInterpretationTests
