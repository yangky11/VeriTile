import VeriTile.Triton.Float.AtomicInterleavingTraceProjection

/-! Traced source executions compose across continuation stacks. A completed
isolated worker has one exact primitive write stream, so a constructive source
trace can identify the stream projected from any shared schedule. -/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

theorem Local.WriteAdvances.single (M : Algebra α) {before after : Local α} {events : List (MemoryWrite α)}
    (ticked : before.tick M before.state.mem = some after)
    (emitted : before.writeEvents M before.state.mem = some events) : before.WriteAdvances M events after := by
  simpa only [List.nil_append] using (Local.WriteAdvances.refl (M := M) (origin := before)).tail ticked emitted

theorem Local.WriteAdvances.trans {M : Algebra α} {first middle last : Local α}
    {events extra : List (MemoryWrite α)} (one : first.WriteAdvances M events middle)
    (two : middle.WriteAdvances M extra last) : first.WriteAdvances M (events ++ extra) last := by
  induction two with
  | refl => simpa only [List.append_nil] using one
  | tail earlier ticked emitted ih => simpa only [List.append_assoc] using ih.tail ticked emitted

theorem Local.writeEvents_append (M : Algebra α) (before : Local α) (tail : List Command)
    (memory : Memory α) (nonempty : before.pending ≠ []) :
    (before.append tail).writeEvents M memory = before.writeEvents M memory := by
  obtain ⟨code,state⟩ := before
  cases code with
  | nil => exact False.elim (nonempty rfl)
  | cons command rest => cases command <;> rfl

theorem Local.WriteAdvances.append {M : Algebra α} {before after : Local α} {events : List (MemoryWrite α)}
    (traced : before.WriteAdvances M events after) (tail : List Command) :
    (before.append tail).WriteAdvances M events (after.append tail) := by
  induction traced with
  | refl => exact Local.WriteAdvances.refl
  | @tail events extra first last earlier ticked emitted ih =>
      have nonempty : first.pending ≠ [] := by
        intro empty
        simp [Local.tick,empty] at ticked
      apply ih.tail (Local.tick_append M first last tail ticked)
      change (first.append tail).writeEvents M first.state.mem = some extra
      rw [Local.writeEvents_append M first tail first.state.mem nonempty]
      exact emitted

inductive Local.WriteSteps (M : Algebra α) : Local α → List (MemoryWrite α) → Local α → Prop where
  | refl (state : Local α) : WriteSteps M state [] state
  | head {before middle after : Local α} {events rest : List (MemoryWrite α)}
      (ticked : before.tick M before.state.mem = some middle)
      (emitted : before.writeEvents M before.state.mem = some events)
      (remaining : WriteSteps M middle rest after) : WriteSteps M before (events ++ rest) after

theorem Local.WriteSteps.trans {M : Algebra α} {first middle last : Local α}
    {events extra : List (MemoryWrite α)} (one : WriteSteps M first events middle)
    (two : WriteSteps M middle extra last) : WriteSteps M first (events ++ extra) last := by
  induction one with
  | refl => simpa only [List.nil_append] using two
  | head ticked emitted remaining ih =>
      simpa only [List.append_assoc] using Local.WriteSteps.head ticked emitted (ih two)

theorem Local.WriteAdvances.steps {M : Algebra α} {first last : Local α} {events : List (MemoryWrite α)}
    (traced : WriteAdvances M first events last) : WriteSteps M first events last := by
  induction traced with
  | refl => exact Local.WriteSteps.refl _
  | tail earlier ticked emitted ih =>
      have single := Local.WriteSteps.head ticked emitted (Local.WriteSteps.refl _)
      simpa only [List.append_nil] using ih.trans single

theorem Local.WriteSteps.complete_unique {M : Algebra α} {first last : Local α} {events : List (MemoryWrite α)}
    (one : WriteSteps M first events last) (done : last.pending = [])
    {other : Local α} {extra : List (MemoryWrite α)} (two : WriteSteps M first extra other)
    (otherDone : other.pending = []) : events = extra ∧ last = other := by
  induction one generalizing other extra with
  | refl state =>
      cases two with
      | refl => exact ⟨rfl,rfl⟩
      | head ticked emitted remaining => simp [Local.tick,done] at ticked
  | @head first middle last events rest ticked emitted remaining ih =>
      cases two with
      | refl => simp [Local.tick,otherDone] at ticked
      | @head _ next other emittedOther restOther advanced generated tail =>
          have same : middle = next := Option.some.inj (ticked.symm.trans advanced)
          subst next
          have operands : events = emittedOther := Option.some.inj (emitted.symm.trans generated)
          obtain ⟨suffix,final⟩ := ih done tail otherDone
          exact ⟨congrArg₂ List.append operands suffix,final⟩

theorem Local.WriteAdvances.complete_unique {M : Algebra α} {first last other : Local α}
    {events extra : List (MemoryWrite α)} (one : WriteAdvances M first events last) (done : last.pending = [])
    (two : WriteAdvances M first extra other) (otherDone : other.pending = []) : events = extra ∧ last = other :=
  one.steps.complete_unique done two.steps otherDone

#axiomsClean Local.WriteAdvances.single
#axiomsClean Local.WriteAdvances.trans
#axiomsClean Local.writeEvents_append
#axiomsClean Local.WriteAdvances.append
#axiomsClean Local.WriteSteps.trans
#axiomsClean Local.WriteAdvances.steps
#axiomsClean Local.WriteSteps.complete_unique
#axiomsClean Local.WriteAdvances.complete_unique
end
end VeriTile.Triton.FP.Structural.Interleaved
