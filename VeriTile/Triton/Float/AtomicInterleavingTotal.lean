import VeriTile.Triton.Float.AtomicInterleavingSchedule

/-! A complete statement schedule exists for finitely many locally total
invocations. The witness schedules real ticks and preserves captured local
state. This is existence only, not equivalence of arbitrary schedules. -/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

def Local.Finishable (M : Algebra α) (thread : Local α) : Prop :=
  ∀ memory, ∃ final, (Local.mk thread.pending { thread.state with mem := memory }).Advances M ⟨[],final⟩

theorem Local.finishable_empty (M : Algebra α) (thread : Local α) (empty : thread.pending = []) :
    thread.Finishable M := by
  intro memory
  refine ⟨{ thread.state with mem := memory },?_⟩
  rw [empty]
  exact Relation.ReflTransGen.refl

theorem Local.finishable_source (M : Algebra α) (body : List ComputeStmt)
    (supported : ∀ statement ∈ body, Supported statement) (state : State α)
    (total : ∀ memory, ∃ final, Structural.run M body { state with mem := memory } = some final) :
    (Local.mk (commands body) state).Finishable M := by
  intro memory
  obtain ⟨final,ran⟩ := total memory
  exact ⟨final,supported_body_completes M body supported _ _ ran⟩

def Configuration.Finishable (jobs : List (Invocation α)) (configuration : Configuration α jobs.length) : Prop :=
  ∀ i, (configuration.locals i).Finishable jobs[i].backend

theorem finish_one (jobs : List (Invocation α)) (selected : Fin jobs.length)
    (initial : Configuration α jobs.length) (ready : initial.Finishable jobs) :
    ∃ schedule final, run jobs schedule initial = some final ∧
      (final.locals selected).pending = [] ∧ final.Finishable jobs ∧
      (∀ other, other ≠ selected → final.locals other = initial.locals other) := by
  obtain ⟨state,advanced⟩ := ready selected initial.memory
  obtain ⟨schedule,final,ran,focused,others,_⟩ :=
    local_advances_schedule jobs selected _ _ advanced initial rfl
  have done : (final.locals selected).pending = [] := congrArg Local.pending focused
  refine ⟨schedule,final,ran,done,?_,others⟩
  intro other
  by_cases same : other = selected
  · subst other
    exact Local.finishable_empty _ _ done
  · rw [others other same]
    exact ready other

theorem finish_list (jobs : List (Invocation α)) (order : List (Fin jobs.length))
    (initial : Configuration α jobs.length) (ready : initial.Finishable jobs) :
    ∃ schedule final, run jobs schedule initial = some final ∧
      (∀ i ∈ order, (final.locals i).pending = []) ∧ final.Finishable jobs ∧
      (∀ i, (initial.locals i).pending = [] → (final.locals i).pending = []) := by
  induction order generalizing initial with
  | nil => exact ⟨[],initial,rfl,by simp,ready,fun _ h => h⟩
  | cons selected rest ih =>
      obtain ⟨first,middle,ranFirst,done,middleReady,others⟩ := finish_one jobs selected initial ready
      obtain ⟨last,final,ranLast,finished,finalReady,preserved⟩ := ih middle middleReady
      refine ⟨first ++ last,final,?_,?_,finalReady,?_⟩
      · rw [run_append,ranFirst]
        exact ranLast
      · intro i inside
        rcases List.mem_cons.mp inside with same | inside
        · subst i
          exact preserved selected done
        · exact finished i inside
      · intro i wasDone
        apply preserved i
        by_cases same : i = selected
        · subst i
          exact done
        · rw [others i same]
          exact wasDone

theorem finish_all (jobs : List (Invocation α)) (initial : Configuration α jobs.length)
    (ready : initial.Finishable jobs) :
    ∃ schedule final, run jobs schedule initial = some final ∧ final.Complete := by
  obtain ⟨schedule,final,ran,done,_,_⟩ := finish_list jobs (List.finRange jobs.length) initial ready
  exact ⟨schedule,final,ran,fun i => done i (List.mem_finRange i)⟩

theorem initial_finishable (jobs : List (Invocation α)) (state : State α)
    (supported : ∀ i : Fin jobs.length, ∀ statement ∈ jobs[i].kernel.surfaceBody, Supported statement)
    (total : ∀ (i : Fin jobs.length) memory, ∃ final,
      exec jobs[i].backend jobs[i].kernel { jobs[i].initial state with mem := memory } = some final) :
    (initial jobs state).Finishable jobs := by
  intro i
  change (Local.mk (commands jobs[i].kernel.surfaceBody) (jobs[i].initial state)).Finishable jobs[i].backend
  apply Local.finishable_source _ _ (supported i)
  intro memory
  obtain ⟨final,ran⟩ := total i memory
  exact ⟨final,ran⟩

theorem grid_completes (jobs : List (Invocation α)) (state : State α)
    (supported : ∀ i : Fin jobs.length, ∀ statement ∈ jobs[i].kernel.surfaceBody, Supported statement)
    (total : ∀ (i : Fin jobs.length) memory, ∃ final,
      exec jobs[i].backend jobs[i].kernel { jobs[i].initial state with mem := memory } = some final) :
    ∃ final, Nonempty (Run jobs state final) := by
  obtain ⟨schedule,result,ran,complete⟩ := finish_all jobs (initial jobs state)
    (initial_finishable jobs state supported total)
  exact ⟨{ state with mem := result.memory },⟨⟨schedule,result,ran,complete,rfl⟩⟩⟩

#axiomsClean Local.finishable_empty
#axiomsClean Local.finishable_source
#axiomsClean finish_one
#axiomsClean finish_list
#axiomsClean finish_all
#axiomsClean initial_finishable
#axiomsClean grid_completes
end
end VeriTile.Triton.FP.Structural.Interleaved
