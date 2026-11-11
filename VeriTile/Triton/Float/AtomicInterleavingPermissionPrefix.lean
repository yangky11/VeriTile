import VeriTile.Triton.Float.AtomicInterleavingPermissionTick
import VeriTile.Triton.Float.AtomicInterleavingOwnedProjection

/-! Sequential source trace certificates discharge every reachable worker's
write permissions, including prefixes ending at loop control or completion. -/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

theorem evaluatePermitted_head (M : Algebra α) (ordinary atomic : RegionName → Nat → Prop)
    (code : List Command) (state : State α) (permitted : evaluatePermitted M ordinary atomic code state) :
    (Local.mk code state).Permitted M ordinary atomic state.mem := by
  cases code with
  | nil => trivial
  | cons command rest =>
    cases command with
    | counted | natural | integer => trivial
    | source statement =>
      by_cases supported : leafSupported statement = true
      · have head := permitted.1
        cases statement <;> simp_all [Local.Permitted,leafSupported,Command.Permissions,Permission.statement]
      · simp [Local.Permitted,supported]

theorem Local.Advances.tracePermission (M : Algebra α) (ordinary atomic : RegionName → Nat → Prop)
    {before after : Local α} (advanced : before.Advances M after)
    (permitted : evaluatePermitted M ordinary atomic before.pending before.state) :
    evaluatePermitted M ordinary atomic after.pending after.state := by
  induction advanced with
  | refl => exact permitted
  | tail _ tick ih => exact (tick_tracePermission M ordinary atomic _ _ _ ih tick).2

theorem source_prefix_permitted (M : Algebra α) (ordinary atomic : RegionName → Nat → Prop)
    (body : List ComputeStmt) (initial : State α) (reference : Local α)
    (permitted : Permission.trace M ordinary atomic body initial)
    (advanced : (Local.mk (commands body) initial).Advances M reference) :
    reference.Permitted M ordinary atomic reference.state.mem :=
  evaluatePermitted_head M ordinary atomic reference.pending reference.state
    (advanced.tracePermission M ordinary atomic ((evaluatePermitted_commands M ordinary atomic body initial).mpr permitted))

theorem Run.project_owned_of_trace (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (owned ordinary atomic : Fin jobs.length → RegionName → Nat → Prop)
    (before after : State α) (executed : Run jobs before after)
    (confined : ∀ i : Fin jobs.length, readOnlyBody regions jobs[i].kernel.surfaceBody)
    (dependent : ∀ i : Fin jobs.length, bodyDependencies regions jobs[i].kernel.surfaceBody)
    (permissions : ∀ i : Fin jobs.length, Permission.trace jobs[i].backend (ordinary i) (atomic i)
      jobs[i].kernel.surfaceBody (jobs[i].initial before))
    (exclusive : ∀ writer reader, writer ≠ reader → ∀ region offset, owned reader region offset →
      ¬ ordinary writer region offset ∧ ¬ atomic writer region offset)
    (i : Fin jobs.length) :
    ∃ isolated, jobs[i].run before = some isolated ∧
      ∀ region offset, owned i region offset → after.mem region offset = isolated.mem region offset := by
  apply executed.project_owned jobs regions owned ordinary atomic before after confined dependent ?_ exclusive i
  intro index reference advanced
  apply source_prefix_permitted jobs[index].backend (ordinary index) (atomic index)
    jobs[index].kernel.surfaceBody (jobs[index].initial before) reference (permissions index)
  cases kernel : jobs[index].kernel
  simpa only [initial,kernel,ComputeKernel.surfaceBody] using advanced

#axiomsClean evaluatePermitted_head
#axiomsClean Local.Advances.tracePermission
#axiomsClean source_prefix_permitted
#axiomsClean Run.project_owned_of_trace
end
end VeriTile.Triton.FP.Structural.Interleaved
