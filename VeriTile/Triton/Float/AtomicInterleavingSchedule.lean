import VeriTile.Triton.Float.AtomicInterleavingSupported

/-! Embed finite local ticks into an actual shared-memory schedule. Other
invocations retain their local controls and registers. This constructs serial
completion witnesses; it does not assert that distinct schedules agree. -/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

def Configuration.focus {count : Nat} (configuration : Configuration α count) (selected : Fin count) : Local α :=
  ⟨(configuration.locals selected).pending,{ (configuration.locals selected).state with mem := configuration.memory }⟩

def Configuration.install {count : Nat} (configuration : Configuration α count) (selected : Fin count)
    (thread : Local α) : Configuration α count :=
  ⟨thread.state.mem,Function.update configuration.locals selected thread⟩

omit [Inhabited α] in
theorem Configuration.focus_install {count : Nat} (configuration : Configuration α count) (selected : Fin count)
    (thread : Local α) : (configuration.install selected thread).focus selected = thread := by
  simp [focus,install]

theorem tick_focus (jobs : List (Invocation α)) (selected : Fin jobs.length)
    (configuration : Configuration α jobs.length) (thread : Local α)
    (ran : (configuration.focus selected).tick jobs[selected].backend (configuration.focus selected).state.mem = some thread) :
    tick jobs selected configuration = some (configuration.install selected thread) := by
  have same : (configuration.focus selected).tick jobs[selected].backend (configuration.focus selected).state.mem =
      (configuration.locals selected).tick jobs[selected].backend configuration.memory := by
    simp only [Configuration.focus,Local.tick]
  rw [same] at ran
  change ((configuration.locals selected).tick jobs[selected].backend configuration.memory).bind
    (fun after => some (Configuration.mk after.state.mem (Function.update configuration.locals selected after))) = _
  rw [ran]
  rfl

theorem run_append (jobs : List (Invocation α)) (first rest : List (Fin jobs.length))
    (initial : Configuration α jobs.length) :
    run jobs (first ++ rest) initial = (run jobs first initial).bind (run jobs rest) := by
  induction first generalizing initial with
  | nil => rfl
  | cons selected tail ih =>
      simp only [List.cons_append,run]
      cases tick jobs selected initial <;> simp [ih]

theorem local_advances_schedule (jobs : List (Invocation α)) (selected : Fin jobs.length)
    (before after : Local α) (advanced : before.Advances jobs[selected].backend after)
    (initial : Configuration α jobs.length) (focusedInitially : initial.focus selected = before) :
    ∃ schedule final, run jobs schedule initial = some final ∧ final.focus selected = after ∧
      (∀ other, other ≠ selected → final.locals other = initial.locals other) ∧
      (∀ index ∈ schedule, index = selected) := by
  induction advanced with
  | refl => exact ⟨[],initial,rfl,focusedInitially,fun _ _ => rfl,by simp⟩
  | @tail middle last earlier one ih =>
      obtain ⟨schedule,current,ran,focused,others,onlySelected⟩ := ih
      have one' : (current.focus selected).tick jobs[selected].backend (current.focus selected).state.mem = some last := by
        simpa only [focused] using one
      have ticked := tick_focus jobs selected current last one'
      refine ⟨schedule ++ [selected],current.install selected last,?_,Configuration.focus_install _ _ _,?_,?_⟩
      · rw [run_append,ran]
        simp only [Option.bind_some,run,ticked]
      · intro other different
        simpa [Configuration.install,Function.update,different] using others other different
      · intro index inside
        rcases List.mem_append.mp inside with inside | inside
        · exact onlySelected index inside
        · simpa using inside

#axiomsClean Configuration.focus_install
#axiomsClean tick_focus
#axiomsClean run_append
#axiomsClean local_advances_schedule
end
end VeriTile.Triton.FP.Structural.Interleaved
