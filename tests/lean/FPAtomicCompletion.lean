import VeriTile.Triton.Float.AtomicInterleavingMetadata
import VeriTile.Triton.Float.ReadOnlyWriteTrace
import VeriTile.Triton.DSL.RetainedSource
import VeriTile.Triton.Float.Control

/-! Completion regression from readable source. Loop bodies really expand
into local ticks, and unsupported atomic shapes and barriers fail admission. -/
namespace FPAtomicCompletionTests
open VeriTile.Triton FP.Structural Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

def nested : RetainedSource := retain_triton_signature ({} : CallSignature) in triton {
  for i in range(0, $(2)) {
    for j in range(0, $(3)) {
      offset = 7
    }
  }
}

def vectorAtomic (input out : RegionName) : RetainedSource := retain_triton_signature
    ({floatingPointers := [("input",.fp32),("out",.fp32)]} : CallSignature) in triton {
  lane = tl.arange(0, $(2))
  tl.atomic_max(out + lane, tl.load(input + lane))
}

def barrier : RetainedSource := retain_triton_signature ({} : CallSignature) in triton {
  tl.debug_barrier()
}

theorem nested_admitted : checkSupportedBody nested.kernel.surfaceBody = Bool.true := by
  simp [nested,ComputeKernel.surfaceBody,checkSupportedBody,checkSupported,leafSupported]
theorem vector_atomic_rejected (input out : RegionName) :
    checkSupportedBody (vectorAtomic input out).kernel.surfaceBody = Bool.false := by
  simp [vectorAtomic,ComputeKernel.surfaceBody,checkSupportedBody,checkSupported,leafSupported]
theorem barrier_rejected : checkSupportedBody barrier.kernel.surfaceBody = Bool.false := by
  simp [barrier,ComputeKernel.surfaceBody,checkSupportedBody,checkSupported,leafSupported]

private theorem range_total {α : Type} [Inhabited α] (M : Algebra α)
    (index : RegName) (stop : Nat) (body : List ComputeStmt)
    (total : ∀ initial : State α, ∃ final, FP.Structural.run M body initial = some final)
    (initial : State α) : ∃ final, range M index 0 stop 1 body initial = some final := by
  have advance : ∀ (i : Nat) (state : State α), i < stop → True →
      ∃ next, FP.Structural.run M body (state.setReg index .nat [] (fun _ => i)) = some next ∧ True := by
    intro i state _ _
    obtain ⟨next,ran⟩ := total (state.setReg index .nat [] (fun _ => i))
    exact ⟨next,ran,True.intro⟩
  obtain ⟨_,final,ran,_,_⟩ := range_invariant M (P := fun _ _ => True) (by decide : 1 ≠ 0)
    advance 0 initial True.intro
  exact ⟨final,ran⟩

theorem nested_runs {α : Type} [Inhabited α] (M : Algebra α) (initial : State α) :
    ∃ final, exec M nested.kernel initial = some final := by
  let leaf : List ComputeStmt := [.assign .real [] "offset" (.alg (.const 7))]
  have leafTotal : ∀ state : State α, ∃ final, FP.Structural.run M leaf state = some final := by
    intro state
    exact ⟨state.setReg "offset" .real [] (fun _ => M.literal none .real 7),by simp [leaf,FP.Structural.run,step,evalExpr,evalOp_unfold]⟩
  let body : List ComputeStmt := [.forRangeDyn "j" (.constNat 0) (.constNat 3) (.constNat 1) leaf]
  have bodyTotal : ∀ state : State α, ∃ final, FP.Structural.run M body state = some final := by
    intro state
    obtain ⟨final,ran⟩ := range_total M "j" 3 leaf leafTotal state
    exact ⟨final,by simpa [body,FP.Structural.run,step,evalOp_unfold] using ran⟩
  obtain ⟨final,ran⟩ := range_total M "i" 2 body bodyTotal initial
  exact ⟨final,by simpa [nested,exec,FP.Structural.run,step,evalOp_unfold,body,leaf] using ran⟩

theorem nested_completes {α : Type} [Inhabited α] (M : Algebra α) (initial : State α) :
    ∃ final, (Local.mk (commands nested.kernel.surfaceBody) initial).Advances M ⟨[],final⟩ := by
  obtain ⟨final,ran⟩ := nested_runs M initial
  exact ⟨final,supported_body_completes M _ (checkSupportedBody_sound _ nested_admitted) _ _ ran⟩

theorem nested_grid_completes {α : Type} [Inhabited α] (jobs : List (Invocation α))
    (initial : State α) (kernels : ∀ i : Fin jobs.length, jobs[i].kernel = nested.kernel) :
    ∃ final, Nonempty (Interleaved.Run jobs initial final) := by
  apply grid_completes jobs initial
  · intro i
    rw [kernels i]
    exact checkSupportedBody_sound _ nested_admitted
  · intro i memory
    rw [kernels i]
    exact nested_runs jobs[i].backend _

theorem nested_preserves_ids {α : Type} [Inhabited α] (M : Algebra α) (initial : State α) :
    ∃ final, exec M nested.kernel initial = some final ∧ final.pids = initial.pids := by
  obtain ⟨final,ran⟩ := nested_runs M initial
  exact ⟨final,ran,supported_run_pids M _ initial final (checkSupportedBody_sound _ nested_admitted) ran⟩

theorem nested_empty_write_trace {α : Type} [Inhabited α] (M : Algebra α) (initial : State α) :
    ∃ final, exec M nested.kernel initial = some final ∧
      (Local.mk (commands nested.kernel.surfaceBody) initial).WriteAdvances M [] ⟨[],final⟩ := by
  obtain ⟨final,executed⟩ := nested_runs M initial
  refine ⟨final,executed,?_⟩
  apply readOnly_body_writeTrace M _ initial final (checkSupportedBody_sound _ nested_admitted) ?_ executed
  simp [nested,ComputeKernel.surfaceBody,readOnlyBody,readOnly]

#axiomsClean nested_empty_write_trace
#axiomsClean nested_preserves_ids
#axiomsClean nested_admitted
#axiomsClean vector_atomic_rejected
#axiomsClean barrier_rejected
#axiomsClean nested_runs
#axiomsClean nested_completes
#axiomsClean nested_grid_completes
end
end FPAtomicCompletionTests
