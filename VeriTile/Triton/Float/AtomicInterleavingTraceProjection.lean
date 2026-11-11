import VeriTile.Triton.Float.AtomicInterleavingWriteAgreement

/-! Preserve each worker's emitted primitive write sequence while projecting
shared schedules onto isolated source execution. Only the merge order differs;
atomic destination words are still supplied by the shared replay. -/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

inductive Local.WriteAdvances (M : Algebra α) (origin : Local α) : List (MemoryWrite α) → Local α → Prop where
  | refl : WriteAdvances M origin [] origin
  | tail {events extra : List (MemoryWrite α)} {before after : Local α}
      (earlier : WriteAdvances M origin events before)
      (ticked : before.tick M before.state.mem = some after)
      (emitted : before.writeEvents M before.state.mem = some extra) :
      WriteAdvances M origin (events ++ extra) after

theorem Local.WriteAdvances.advances {M : Algebra α} {origin final : Local α} {events : List (MemoryWrite α)}
    (traced : WriteAdvances M origin events final) : origin.Advances M final := by
  induction traced with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ ticked _ ih => exact ih.tail ticked

def workerEvents {count : Nat} (events : List (Fin count × MemoryWrite α)) (worker : Fin count) : List (MemoryWrite α) :=
  events.filterMap (fun entry => if entry.1 = worker then some entry.2 else none)

theorem workerEvents_append {count : Nat} (first second : List (Fin count × MemoryWrite α)) (worker : Fin count) :
    workerEvents (first ++ second) worker = workerEvents first worker ++ workerEvents second worker := by
  simp only [workerEvents,List.filterMap_append]

theorem workerEvents_selected {count : Nat} (events : List (MemoryWrite α)) (worker : Fin count) :
    workerEvents (events.map (fun event => (worker,event))) worker = events := by
  simp [workerEvents,List.filterMap_map]

theorem workerEvents_other {count : Nat} (events : List (MemoryWrite α)) (worker other : Fin count) (different : worker ≠ other) :
    workerEvents (events.map (fun event => (worker,event))) other = [] := by
  simp [workerEvents,List.filterMap_map,different]

def Configuration.TraceProjects (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (origins : Fin jobs.length → Local α) (history : List (Fin jobs.length × MemoryWrite α))
    (state : Configuration α jobs.length) : Prop :=
  ∀ i, ∃ reference : Local α,
    (origins i).WriteAdvances jobs[i].backend (workerEvents history i) reference ∧
    reference.pending = (state.focus i).pending ∧
    reference.state.AgreesOn regions (state.focus i).state

theorem tick_trace_projects (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (origins : Fin jobs.length → Local α) (selected : Fin jobs.length)
    (history events : List (Fin jobs.length × MemoryWrite α)) (before after : Configuration α jobs.length)
    (confined : before.ReadOnly regions) (dependent : before.Dependencies regions)
    (projected : before.TraceProjects jobs regions origins history)
    (generated : tickWriteEvents jobs selected before = some events)
    (ran : tick jobs selected before = some after) :
    after.TraceProjects jobs regions origins (history ++ events) := by
  obtain ⟨extra,emitted,tagged⟩ := Option.map_eq_some_iff.mp generated
  subst events
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
    have emittedReference : reference.writeEvents jobs[selected].backend reference.state.mem = some extra := by
      have equal := Local.writeEvents_agree jobs[selected].backend regions reference.pending
        (pending ▸ dependent selected) reference.state (before.focus selected).state related
      have emitted' : (Local.mk reference.pending (before.focus selected).state).writeEvents
          jobs[selected].backend (before.focus selected).state.mem = some extra := by
        simpa only [pending,Configuration.focus,Local.writeEvents] using emitted
      exact equal.trans emitted'
    refine ⟨other,?_,?_,?_⟩
    · rw [workerEvents_append,workerEvents_selected]
      exact earlier.tail executed emittedReference
    · simpa [Configuration.focus] using control.symm
    · simpa [Configuration.focus] using same.symm
  · refine ⟨reference,?_,?_,?_⟩
    · rw [workerEvents_append,workerEvents_other extra selected i (Ne.symm selectedHere),List.append_nil]
      exact earlier
    · simpa [Configuration.focus,Function.update,selectedHere] using pending
    · refine ⟨?_,?_,?_,?_,?_⟩
      · simpa [Configuration.focus,Function.update,selectedHere] using related.registers
      · simpa [Configuration.focus,Function.update,selectedHere] using related.programs
      · simpa [Configuration.focus,Function.update,selectedHere] using related.grid
      · simpa [Configuration.focus,Function.update,selectedHere] using related.undefined
      · intro region member
        exact (related.memory region member).trans (framed region member).symm

theorem run_trace_projects (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (origins : Fin jobs.length → Local α) (history : List (Fin jobs.length × MemoryWrite α))
    (schedule : List (Fin jobs.length)) (before after : Configuration α jobs.length)
    (confined : before.ReadOnly regions) (dependent : before.Dependencies regions)
    (projected : before.TraceProjects jobs regions origins history)
    (ran : run jobs schedule before = some after) :
    ∃ events, runWriteEvents jobs schedule before = some events ∧
      after.TraceProjects jobs regions origins (history ++ events) := by
  induction schedule generalizing before history with
  | nil =>
      simp only [run,Option.some.injEq] at ran
      subst after
      exact ⟨[],rfl,by simpa only [List.append_nil] using projected⟩
  | cons selected rest ih =>
      obtain ⟨next,advanced,remaining⟩ := Option.bind_eq_some_iff.mp ran
      obtain ⟨first,generated,_⟩ := tick_write_events jobs regions selected before next dependent advanced
        (before.focus selected).state
      obtain ⟨tail,generatedTail,projectedTail⟩ := ih (history ++ first) next
        (tick_readOnly jobs regions selected before next confined advanced).1
        (tick_dependencies jobs regions selected before next dependent advanced)
        (tick_trace_projects jobs regions origins selected history first before next confined dependent projected generated advanced)
        remaining
      exact ⟨first ++ tail,by simp [runWriteEvents,generated,advanced,generatedTail],
        by simpa only [List.append_assoc] using projectedTail⟩

theorem initial_trace_projects (jobs : List (Invocation α)) (regions : RegionName → Prop) (state : State α) :
    (initial jobs state).TraceProjects jobs regions (initial jobs state).locals [] := by
  intro i
  refine ⟨(initial jobs state).locals i,Local.WriteAdvances.refl,rfl,?_⟩
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro region member
  simp [initial,Configuration.focus]

theorem Run.project_trace (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (before after : State α) (executed : Run jobs before after)
    (confined : ∀ i : Fin jobs.length, readOnlyBody regions jobs[i].kernel.surfaceBody)
    (dependent : ∀ i : Fin jobs.length, bodyDependencies regions jobs[i].kernel.surfaceBody) :
    ∃ events, runWriteEvents jobs executed.schedule (initial jobs before) = some events ∧
      ∀ i : Fin jobs.length, ∃ isolated, jobs[i].run before = some isolated ∧
        ((initial jobs before).locals i).WriteAdvances jobs[i].backend (workerEvents events i) ⟨[],isolated⟩ := by
  obtain ⟨events,generated,projected⟩ := run_trace_projects jobs regions (initial jobs before).locals []
    executed.schedule (initial jobs before) executed.result
    (initial_readOnly jobs regions before confined) (initial_dependencies jobs regions before dependent)
    (initial_trace_projects jobs regions before) executed.executed
  refine ⟨events,generated,?_⟩
  intro i
  obtain ⟨reference,traced,pending,_⟩ := projected i
  have completed : reference.pending = [] := pending.trans (executed.complete i)
  have denoted := traced.advances.denotes jobs[i].backend
  rw [completed,evaluate] at denoted
  refine ⟨reference.state,?_,?_⟩
  · change exec jobs[i].backend jobs[i].kernel (jobs[i].initial before) = some reference.state
    change evaluate jobs[i].backend
      (match jobs[i].kernel with | .mk _ _ body => commands body) (jobs[i].initial before) = _ at denoted
    cases kernel : jobs[i].kernel
    simp only [kernel,exec] at *
    exact (evaluate_commands _ _ _).symm.trans denoted
  · cases reference with
    | mk code state =>
      change code = [] at completed
      subst code
      simpa only [List.nil_append] using traced

#axiomsClean run_trace_projects
#axiomsClean initial_trace_projects
#axiomsClean Run.project_trace
#axiomsClean Local.WriteAdvances.advances
#axiomsClean workerEvents_append
#axiomsClean workerEvents_selected
#axiomsClean workerEvents_other
#axiomsClean tick_trace_projects
end
end VeriTile.Triton.FP.Structural.Interleaved
