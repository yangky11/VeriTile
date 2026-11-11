import VeriTile.Triton.Float.AtomicInterleavingPermissionPrefix
import VeriTile.Triton.Float.ReadOnlyPermission
import VeriTile.Triton.DSL.RetainedSource

/-! Actual retained-source workers share an output allocation while owning
individual cells. The source trace discharges prefix permissions; arbitrary
successful schedules preserve each owner's isolated source result. -/
namespace FPCellOwnershipTests
open VeriTile.Triton FP.Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

def copyWorker (input out : RegionName) : RetainedSource := retain_triton_signature
    ({floatingPointers := [("input",.fp32),("out",.fp32)]} : CallSignature) in triton {
  tl.store(out + tl.program_id(0), tl.load(input + tl.program_id(0)))
}

def owns (out : RegionName) (worker : Nat) (region : RegionName) (offset : Nat) : Prop :=
  region = out ∧ offset = worker

theorem copy_permissions {α : Type} [Inhabited α] (M : Algebra α) (input out : RegionName) (state : State α) :
    Permission.trace M (owns out (state.pids 0)) (fun _ _ => False) (copyWorker input out).kernel.surfaceBody state := by
  simp [copyWorker,ComputeKernel.surfaceBody,Permission.trace_cons,Permission.statement,leafWritePermitted,
    writePermitted,Safety.maskActive,evalOp_unfold,Region.cast,owns]

theorem copy_readOnly (input out : RegionName) (separate : out ≠ input) :
    readOnlyBody (fun region => region = input) (copyWorker input out).kernel.surfaceBody := by
  simp [copyWorker,ComputeKernel.surfaceBody,readOnlyBody,readOnly,accessOutside,Region.cast,separate]

theorem copy_dependencies (input out : RegionName) :
    bodyDependencies (fun region => region = input) (copyWorker input out).kernel.surfaceBody := by
  simp only [copyWorker,ComputeKernel.surfaceBody,bodyDependencies,readDependencies,accessReads,maskReads,Region.cast]
  repeat first | rfl | constructor

theorem copy_grid_owned {α : Type} [Inhabited α] (input out : RegionName) (separate : out ≠ input)
    (jobs : List (Invocation α)) (before after : State α)
    (sources : ∀ i : Fin jobs.length, jobs[i].kernel = (copyWorker input out).kernel)
    (distinct : Function.Injective (fun i : Fin jobs.length => (jobs[i].initial before).pids 0))
    (executed : Interleaved.Run jobs before after) (i : Fin jobs.length) :
    ∃ isolated, jobs[i].run before = some isolated ∧
      after.mem out ((jobs[i].initial before).pids 0) = isolated.mem out ((jobs[i].initial before).pids 0) := by
  let owned := fun index : Fin jobs.length => owns out ((jobs[index].initial before).pids 0)
  obtain ⟨isolated,ran,cells⟩ := Interleaved.Run.project_owned_of_trace jobs (fun region => region = input)
    owned owned (fun _ _ _ => False) before after executed
    (by intro index; rw [sources index]; exact copy_readOnly input out separate)
    (by intro index; rw [sources index]; exact copy_dependencies input out)
    (by intro index; rw [sources index]; exact copy_permissions jobs[index].backend input out _)
    (by
      intro writer reader different region offset member
      refine ⟨?_,by simp⟩
      intro written
      apply different
      apply distinct
      exact written.2.symm.trans member.2) i
  exact ⟨isolated,ran,cells out _ ⟨rfl,rfl⟩⟩

#axiomsClean copy_permissions
#axiomsClean copy_readOnly
#axiomsClean copy_dependencies
#axiomsClean copy_grid_owned
end
end FPCellOwnershipTests
