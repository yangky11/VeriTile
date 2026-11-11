import VeriTile.Triton.Float.AtomicInterleavingTraceComposition

/-! Straight-line source blocks produce primitive event streams by evaluating
their actual statements. Their traces compose with source control blocks via
the shared continuation theorem; no whole-block numerical oracle is used. -/
namespace VeriTile.Triton.FP.Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

def flatWriteEvents (M : Algebra α) : List ComputeStmt → State α → Option (List (MemoryWrite α))
  | [],_ => some []
  | statement :: rest,state => do
      let events ← leafWriteEvents M statement state
      let next ← step M statement state
      let tail ← flatWriteEvents M rest next
      return events ++ tail

theorem flatWriteEvents_exists (M : Algebra α) (body : List ComputeStmt) (initial final : State α)
    (admitted : ∀ statement ∈ body, leafWriteTraceSupported statement)
    (executed : run M body initial = some final) : ∃ events, flatWriteEvents M body initial = some events := by
  induction body generalizing initial with
  | nil => exact ⟨[],rfl⟩
  | cons statement rest ih =>
      simp only [run] at executed
      obtain ⟨next,advanced,remaining⟩ := Option.bind_eq_some_iff.mp executed
      obtain ⟨first,generated,_⟩ := step_write_events M statement initial next (admitted _ (by simp)) advanced
      obtain ⟨tail,generatedTail⟩ := ih next (by intro st member; exact admitted st (by simp [member])) remaining
      exact ⟨first ++ tail,by simp [flatWriteEvents,generated,advanced,generatedTail]⟩

theorem flatWriteEvents_trace (M : Algebra α) (body : List ComputeStmt) (initial final : State α)
    (supported : ∀ statement ∈ body, Interleaved.leafSupported statement = true)
    (executed : run M body initial = some final) (events : List (MemoryWrite α))
    (generated : flatWriteEvents M body initial = some events) :
    (Interleaved.Local.mk (Interleaved.commands body) initial).WriteAdvances M events ⟨[],final⟩ := by
  induction body generalizing initial events with
  | nil =>
      simp only [run,Option.some.injEq] at executed
      simp only [flatWriteEvents,Option.some.injEq] at generated
      subst final
      subst events
      exact Interleaved.Local.WriteAdvances.refl
  | cons statement rest ih =>
      simp only [run] at executed
      obtain ⟨next,advanced,remaining⟩ := Option.bind_eq_some_iff.mp executed
      simp only [flatWriteEvents] at generated
      obtain ⟨first,generatedFirst,generatedRest⟩ := Option.bind_eq_some_iff.mp generated
      simp only [advanced,bind,Option.bind_some] at generatedRest
      obtain ⟨tail,generatedTail,returned⟩ := Option.bind_eq_some_iff.mp generatedRest
      have equal := Option.some.inj returned
      subst events
      have leaf := supported statement (by simp)
      have one : (Interleaved.Local.mk (Interleaved.commands (statement :: rest)) initial).WriteAdvances M first
          ⟨Interleaved.commands rest,next⟩ := by
        apply Interleaved.Local.WriteAdvances.single M
        · simp [Interleaved.Local.tick,Interleaved.commands,leaf,advanced]
        · simpa only [Interleaved.Local.writeEvents,Interleaved.commands,List.map_cons,leaf,ite_true] using generatedFirst
      exact one.trans (ih next (by intro st member; exact supported st (by simp [member])) remaining tail generatedTail)

#axiomsClean flatWriteEvents_exists
#axiomsClean flatWriteEvents_trace
end
end VeriTile.Triton.FP.Structural
