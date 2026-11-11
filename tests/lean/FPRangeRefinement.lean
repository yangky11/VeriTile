import VeriTile.Triton.Float.RangeRefinement
import VeriTile.Meta.StatementAudit

/-! Ordered recurrence readback from actual source counter bindings. The
non-associative decimal recurrence distinguishes visits and their order. -/
namespace FPRangeRefinementTests
open VeriTile.Triton FP.Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false

def body : List ComputeStmt := [
  .alg (.assign .nat [] "acc" (.add .nat .nil
    (.mul .nat .nil (.ref .nat [] "acc") (.constNat 10)) (.ref .nat [] "i")))]

def related {α : Type} (state : State α) (value : Nat) : Prop :=
  state.regs .nat [] "acc" = some (fun _ => value)

theorem advance {α : Type} [Inhabited α] (M : Algebra α) (stride stage : Nat)
    (state : State α) (value : Nat) (bound : related state value) :
    ∃ next, run M body (state.setReg "i" .nat [] (fun _ => stage*stride)) = some next ∧
      related next (value*10+stage*stride) := by
  refine ⟨(state.setReg "i" .nat [] (fun _ => stage*stride)).setReg "acc" .nat []
    (fun _ => value*10+stage*stride),?_,?_⟩
  · simp [body,run,step,stepAlg,evalOp_unfold,numeric,related] at bound ⊢
    rw [bound]
    rfl
  · simp [related]

theorem overshooting_nonzero_start {α : Type} [Inhabited α] (M : Algebra α) (initial : State α)
    (seed : related initial 0) :
    ∃ final, range M "i" 4 13 4 body initial = some final ∧ related final 492 := by
  have step : ∀ stage state value, stage*4 < 13 → related state value →
      ∃ next, run M body (state.setReg "i" .nat [] (fun _ => stage*4)) = some next ∧
        related next (value*10+stage*4) := by
    intro stage state value _ bound
    exact advance M 4 stage state value bound
  simpa [List.range',List.foldl] using range_fold_refines M "i" 13 4 body related
    (fun value stage => value*10+stage*4) (by decide) step 1 3 initial 0
    (by intro stage lo hi; omega) (by decide) seed

theorem zero_based_partial_tile {α : Type} [Inhabited α] (M : Algebra α) (initial : State α)
    (seed : related initial 0) :
    ∃ final, range M "i" 0 10 4 body initial = some final ∧ related final 48 := by
  have step : ∀ stage state value, stage*4 < 10 → related state value →
      ∃ next, run M body (state.setReg "i" .nat [] (fun _ => stage*4)) = some next ∧
        related next (value*10+stage*4) := by
    intro stage state value _ bound
    exact advance M 4 stage state value bound
  simpa [List.range,List.range.loop,List.foldl] using range_zero_fold_refines M "i" 10 4 body related
    (fun value stage => value*10+stage*4) (by decide) step initial 0 seed

theorem empty_range {α : Type} [Inhabited α] (M : Algebra α) (initial : State α)
    (seed : related initial 7) :
    ∃ final, range M "i" 0 0 4 body initial = some final ∧ related final 7 := by
  simpa using range_zero_fold_refines M "i" 0 4 body related
    (fun value stage => value*10+stage*4) (by decide)
    (by intro stage state value impossible; omega) initial 7 seed

#axiomsClean stage_lt_ceil_iff
#axiomsClean range_fold_refines
#axiomsClean range_zero_fold_refines
#axiomsClean advance
#axiomsClean overshooting_nonzero_start
#axiomsClean zero_based_partial_tile
#axiomsClean empty_range
end
end FPRangeRefinementTests
