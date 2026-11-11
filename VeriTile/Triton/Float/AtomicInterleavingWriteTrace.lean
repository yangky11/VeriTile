import VeriTile.Triton.Float.WriteTraceDependency
import VeriTile.Triton.Float.AtomicInterleavingControlMemory
import VeriTile.Triton.Float.AtomicInterleavingProjection

/-! Instrumentation of the actual source scheduler records primitive writes
and their executing worker. The resulting ordered trace reconstructs shared
memory, including seeded atomic observations, without commuting updates. -/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

def Local.writeEvents (M : Algebra α) (thread : Local α) (memory : Memory α) : Option (List (MemoryWrite α)) :=
  match thread.pending with
  | .source statement :: _ =>
      if leafSupported statement then leafWriteEvents M statement { thread.state with mem := memory } else some []
  | _ => some []

theorem Local.tick_write_events (M : Algebra α) (regions : RegionName → Prop)
    (before after : Local α) (memory : Memory α) (dependent : pendingDependencies regions before.pending)
    (ran : before.tick M memory = some after) :
    ∃ events, before.writeEvents M memory = some events ∧
      after.state.mem = (MemoryWrite.applyAll events { before.state with mem := memory }).mem := by
  obtain ⟨code,state⟩ := before
  cases code with
  | nil => simp [tick] at ran
  | cons command rest =>
    cases command with
    | source statement =>
      by_cases leaf : leafSupported statement = true
      · have admitted := readDependencies_leaf_writeTrace regions statement
          ((pendingDependencies_cons regions _ _).mp dependent).1 leaf
        simp only [tick,leaf,ite_true] at ran
        obtain ⟨next,stepped,returned⟩ := Option.bind_eq_some_iff.mp ran
        have equal := Option.some.inj returned
        subst after
        obtain ⟨events,generated,framed⟩ := step_write_events M statement _ next admitted stepped
        exact ⟨events,by simpa only [writeEvents,leaf,ite_true] using generated,framed⟩
      · refine ⟨[],by simp [writeEvents,leaf],?_⟩
        exact Local.tick_control_memory M _ after memory (by simpa [leafHead] using leaf) ran
    | counted | natural | integer =>
      exact ⟨[],rfl,Local.tick_control_memory M _ after memory rfl ran⟩

def tickWriteEvents (jobs : List (Invocation α)) (selected : Fin jobs.length)
    (before : Configuration α jobs.length) : Option (List (Fin jobs.length × MemoryWrite α)) :=
  ((before.locals selected).writeEvents jobs[selected].backend before.memory).map
    (fun events => events.map (fun event => (selected,event)))

theorem tick_write_events (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (selected : Fin jobs.length) (before after : Configuration α jobs.length)
    (dependent : before.Dependencies regions) (ran : tick jobs selected before = some after) (anchor : State α) :
    ∃ events, tickWriteEvents jobs selected before = some events ∧
      after.memory = (MemoryWrite.applyAll (events.map Prod.snd) { anchor with mem := before.memory }).mem := by
  obtain ⟨thread,ticked,returned⟩ := Option.bind_eq_some_iff.mp ran
  have equal := Option.some.inj returned
  subst after
  obtain ⟨events,generated,framed⟩ := Local.tick_write_events jobs[selected].backend regions
    (before.locals selected) thread before.memory (dependent selected) ticked
  refine ⟨events.map (fun event => (selected,event)),?_,?_⟩
  · change Option.map _ ((before.locals selected).writeEvents jobs[selected].backend before.memory) = _
    rw [generated]
    rfl
  · simpa only [List.map_map,Function.comp_def,List.map_id_fun',id_eq] using
      framed.trans (MemoryWrite.applyAll_memory events _ { anchor with mem := before.memory } rfl)

def runWriteEvents (jobs : List (Invocation α)) : List (Fin jobs.length) →
    Configuration α jobs.length → Option (List (Fin jobs.length × MemoryWrite α))
  | [],_ => some []
  | selected :: rest,before => do
      let events ← tickWriteEvents jobs selected before
      let next ← tick jobs selected before
      let tail ← runWriteEvents jobs rest next
      return events ++ tail

theorem run_write_events (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (schedule : List (Fin jobs.length)) (before after : Configuration α jobs.length)
    (dependent : before.Dependencies regions) (ran : run jobs schedule before = some after) (anchor : State α) :
    ∃ events, runWriteEvents jobs schedule before = some events ∧
      after.memory = (MemoryWrite.applyAll (events.map Prod.snd) { anchor with mem := before.memory }).mem := by
  induction schedule generalizing before with
  | nil => simp only [run,Option.some.injEq] at ran; subst after; exact ⟨[],rfl,rfl⟩
  | cons selected rest ih =>
      obtain ⟨next,advanced,remaining⟩ := Option.bind_eq_some_iff.mp ran
      obtain ⟨first,generated,framed⟩ := tick_write_events jobs regions selected before next dependent advanced anchor
      obtain ⟨tail,generatedTail,framedTail⟩ := ih next
        (tick_dependencies jobs regions selected before next dependent advanced) remaining
      refine ⟨first ++ tail,by simp [runWriteEvents,generated,advanced,generatedTail],?_⟩
      rw [List.map_append,MemoryWrite.applyAll_append]
      exact framedTail.trans (MemoryWrite.applyAll_memory _ _ _ framed)

theorem Run.write_trace (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (before after : State α) (executed : Run jobs before after)
    (dependent : ∀ i : Fin jobs.length, bodyDependencies regions jobs[i].kernel.surfaceBody) :
    ∃ events, runWriteEvents jobs executed.schedule (initial jobs before) = some events ∧
      ∀ region offset, after.mem region offset =
        (events.map Prod.snd).foldl (fun old event => event.atCell region offset old) (before.mem region offset) := by
  obtain ⟨events,generated,framed⟩ := run_write_events jobs regions executed.schedule (initial jobs before)
    executed.result (initial_dependencies jobs regions before dependent) executed.executed before
  refine ⟨events,generated,?_⟩
  intro region offset
  rw [executed.readback,framed,MemoryWrite.applyAll_read]
  rfl

#axiomsClean Local.tick_write_events
#axiomsClean tick_write_events
#axiomsClean run_write_events
#axiomsClean Run.write_trace
end
end VeriTile.Triton.FP.Structural.Interleaved
