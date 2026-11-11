import VeriTile.Triton.Float.AtomicInterleavingAgreement
import VeriTile.Triton.Float.AtomicInterleavingSchedule

/-! Project each worker of an arbitrary successful shared-memory schedule onto
actual isolated source ticks. Fixed input regions suffice for equality of local
control and registers. Writable memory, including atomic destinations, is not
asserted equal. -/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

def Configuration.Dependencies {count : Nat} (regions : RegionName → Prop)
    (state : Configuration α count) : Prop :=
  ∀ i, pendingDependencies regions (state.locals i).pending

theorem tick_dependencies (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (selected : Fin jobs.length) (before after : Configuration α jobs.length)
    (dependent : before.Dependencies regions) (ran : tick jobs selected before = some after) :
    after.Dependencies regions := by
  obtain ⟨next,advanced,returned⟩ := Option.bind_eq_some_iff.mp ran
  have equal := Option.some.inj returned
  subst after
  have nextDependent := Local.tick_dependencies jobs[selected].backend regions
    (before.locals selected) next before.memory (dependent selected) advanced
  intro i
  by_cases equal : i = selected
  · subst i; simpa using nextDependent
  · simpa [Function.update,equal] using dependent i

/-- Each worker has an actual isolated execution prefix with the same control,
registers and input memory as its current shared-memory focus. -/
def Configuration.Projects (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (origins : Fin jobs.length → Local α) (state : Configuration α jobs.length) : Prop :=
  ∀ i, ∃ reference : Local α,
    (origins i).Advances jobs[i].backend reference ∧
    reference.pending = (state.focus i).pending ∧
    reference.state.AgreesOn regions (state.focus i).state

theorem tick_projects (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (origins : Fin jobs.length → Local α) (selected : Fin jobs.length)
    (before after : Configuration α jobs.length)
    (confined : before.ReadOnly regions) (dependent : before.Dependencies regions)
    (projected : before.Projects jobs regions origins)
    (ran : tick jobs selected before = some after) :
    after.Projects jobs regions origins := by
  obtain ⟨next,advanced,returned⟩ := Option.bind_eq_some_iff.mp ran
  have equal := Option.some.inj returned
  subst after
  have framed := (Local.tick_readOnly jobs[selected].backend regions
    (before.locals selected) next before.memory (confined selected) advanced).2
  intro i
  obtain ⟨reference,earlier,pending,related⟩ := projected i
  by_cases selectedHere : i = selected
  · subst i
    have advanced' : (Local.mk reference.pending (before.focus selected).state).tick
        jobs[selected].backend (before.focus selected).state.mem = some next := by
      simpa only [pending,Configuration.focus,Local.tick] using advanced
    obtain ⟨other,executed,control,same⟩ := tick_agrees jobs[selected].backend regions reference.pending
      (pending ▸ confined selected) (pending ▸ dependent selected)
      (before.focus selected).state reference.state related.symm next advanced'
    refine ⟨other,earlier.tail executed,?_,?_⟩
    · simpa [Configuration.focus] using control.symm
    · simpa [Configuration.focus] using same.symm
  · refine ⟨reference,earlier,?_,?_⟩
    · simpa [Configuration.focus,Function.update,selectedHere] using pending
    · refine ⟨?_,?_,?_,?_,?_⟩
      · simpa [Configuration.focus,Function.update,selectedHere] using related.registers
      · simpa [Configuration.focus,Function.update,selectedHere] using related.programs
      · simpa [Configuration.focus,Function.update,selectedHere] using related.grid
      · simpa [Configuration.focus,Function.update,selectedHere] using related.undefined
      · intro region member
        exact (related.memory region member).trans (framed region member).symm

theorem run_projects (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (origins : Fin jobs.length → Local α) (schedule : List (Fin jobs.length))
    (before after : Configuration α jobs.length)
    (confined : before.ReadOnly regions) (dependent : before.Dependencies regions)
    (projected : before.Projects jobs regions origins)
    (ran : run jobs schedule before = some after) :
    after.Projects jobs regions origins := by
  induction schedule generalizing before with
  | nil => simp only [run,Option.some.injEq] at ran; subst after; exact projected
  | cons selected rest ih =>
      obtain ⟨next,advanced,remaining⟩ := Option.bind_eq_some_iff.mp ran
      exact ih next (tick_readOnly jobs regions selected before next confined advanced).1
        (tick_dependencies jobs regions selected before next dependent advanced)
        (tick_projects jobs regions origins selected before next confined dependent projected advanced)
        remaining

omit [Inhabited α] in
theorem initial_dependencies (jobs : List (Invocation α)) (regions : RegionName → Prop) (state : State α)
    (dependent : ∀ i : Fin jobs.length, bodyDependencies regions jobs[i].kernel.surfaceBody) :
    (initial jobs state).Dependencies regions := by
  intro i
  change pendingDependencies regions (match jobs[i].kernel with | .mk _ _ body => commands body)
  have source := dependent i
  cases kernel : jobs[i].kernel
  simp only [kernel,ComputeKernel.surfaceBody] at source
  exact (commands_dependencies regions _).mpr source

/-- Origin local states include the launch's actual argument and program-ID bindings. -/
theorem initial_projects (jobs : List (Invocation α)) (regions : RegionName → Prop) (state : State α) :
    (initial jobs state).Projects jobs regions (initial jobs state).locals := by
  intro i
  refine ⟨(initial jobs state).locals i,Relation.ReflTransGen.refl,rfl,?_⟩
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro region member
  simp [initial,Configuration.focus]

/-- Completion of an arbitrary schedule entails a genuine isolated source
execution for each invocation with identical final local registers. Shared
writable destinations are intentionally absent from the agreement conclusion. -/
theorem Run.project (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (before after : State α) (executed : Run jobs before after)
    (confined : ∀ i : Fin jobs.length, readOnlyBody regions jobs[i].kernel.surfaceBody)
    (dependent : ∀ i : Fin jobs.length, bodyDependencies regions jobs[i].kernel.surfaceBody)
    (i : Fin jobs.length) :
    ∃ isolated, jobs[i].run before = some isolated ∧
      isolated.AgreesOn regions (executed.result.focus i).state := by
  obtain ⟨reference,advanced,pending,related⟩ := run_projects jobs regions
    (initial jobs before).locals executed.schedule (initial jobs before) executed.result
    (initial_readOnly jobs regions before confined) (initial_dependencies jobs regions before dependent)
    (initial_projects jobs regions before) executed.executed i
  have completed : reference.pending = [] := pending.trans (executed.complete i)
  have denoted := advanced.denotes jobs[i].backend
  rw [completed,evaluate] at denoted
  refine ⟨reference.state,?_,related⟩
  change exec jobs[i].backend jobs[i].kernel (jobs[i].initial before) = some reference.state
  change evaluate jobs[i].backend
    (match jobs[i].kernel with | .mk _ _ body => commands body) (jobs[i].initial before) = _ at denoted
  cases kernel : jobs[i].kernel
  simp only [kernel,exec] at *
  exact (evaluate_commands _ _ _).symm.trans denoted

#axiomsClean initial_dependencies
#axiomsClean initial_projects
#axiomsClean Run.project
#axiomsClean tick_dependencies
#axiomsClean tick_projects
#axiomsClean run_projects
end
end VeriTile.Triton.FP.Structural.Interleaved
