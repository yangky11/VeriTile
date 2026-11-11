import VeriTile.Triton.Float.ComputeReadDependency
import VeriTile.Triton.Float.AtomicInterleavingReadOnly
import VeriTile.Triton.DSL.RetainedSource

/-! Retained-source regressions include a nested masked fallback read and a
loop with ordinary stores plus an ordered scalar maximum. -/
namespace FPReadDependencyTests
open VeriTile.Triton FP.Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

def maskedRead (input fallback : RegionName) : RetainedSource := retain_triton_signature
    ({floatingPointers := [("input",.fp32),("fallback",.fp32)]} : CallSignature) in triton {
  value = tl.load(input, tl.program_id(0) < 1, other=tl.load(fallback))
}

def assignmentReads (regions : RegionName → Prop) : List ComputeStmt → Prop
  | [.assign _ _ _ expression] => ExprReads regions expression
  | _ => False

theorem masked_dependencies (input fallback : RegionName) :
    assignmentReads (fun region => region = input ∨ region = fallback) (maskedRead input fallback).kernel.surfaceBody := by
  simp only [maskedRead,ComputeKernel.surfaceBody,assignmentReads]
  repeat first | (solve | simp [Region.cast]) | constructor

def worker (input out observation : RegionName) : RetainedSource := retain_triton_signature
    ({floatingPointers := [("input",.fp32),("out",.fp32),("observation",.fp32)]} : CallSignature) in triton {
  for i in range(0, $(2)) {
    value = tl.load(input + i)
    tl.store(out + i, value)
    tl.atomic_max(observation, value)
  }
}

theorem worker_readOnly (input out observation : RegionName) (outSeparate : out ≠ input) (observationSeparate : observation ≠ input) :
    readOnlyBody (fun region => region = input) (worker input out observation).kernel.surfaceBody := by
  simp [worker,ComputeKernel.surfaceBody,readOnlyBody,readOnly,accessOutside,Region.cast,outSeparate,observationSeparate]

theorem worker_grid_preserves_input {α : Type} [Inhabited α] (input out observation : RegionName)
    (outSeparate : out ≠ input) (observationSeparate : observation ≠ input)
    (jobs : List (Invocation α)) (before after : State α)
    (sources : ∀ i : Fin jobs.length, jobs[i].kernel = (worker input out observation).kernel)
    (executed : Interleaved.Run jobs before after) : after.mem input = before.mem input := by
  apply Interleaved.Run.readOnly jobs (fun region => region = input) before after executed
  · intro i
    rw [sources i]
    exact worker_readOnly input out observation outSeparate observationSeparate
  · rfl

theorem worker_alias_rejected (input observation : RegionName) :
    ¬ readOnlyBody (fun region => region = input) (worker input input observation).kernel.surfaceBody := by
  simp [worker,ComputeKernel.surfaceBody,readOnlyBody,readOnly,accessOutside,Region.cast]

#axiomsClean worker_alias_rejected
#axiomsClean masked_dependencies
#axiomsClean worker_readOnly
#axiomsClean worker_grid_preserves_input
end
end FPReadDependencyTests
