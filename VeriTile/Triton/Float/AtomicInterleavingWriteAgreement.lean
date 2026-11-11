import VeriTile.Triton.Float.WriteTraceAgreement
import VeriTile.Triton.Float.AtomicInterleavingWriteTrace

/-! A worker's actual emitted writes agree with its isolated source prefix
when declared read regions agree. This compares operands and primitive event
identity; atomic old words remain supplied by shared-memory replay. -/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

theorem Local.writeEvents_agree (M : Algebra α) (regions : RegionName → Prop)
    (code : List Command) (dependent : pendingDependencies regions code)
    (first second : State α) (same : first.AgreesOn regions second) :
    (Local.mk code first).writeEvents M first.mem = (Local.mk code second).writeEvents M second.mem := by
  cases code with
  | nil => rfl
  | cons command rest =>
    cases command with
    | source statement =>
      by_cases leaf : leafSupported statement = true
      · simp only [writeEvents,leaf,ite_true]
        exact leafWriteEvents_agree M regions statement
          ((pendingDependencies_cons regions _ _).mp dependent).1 first second same
      · simp [writeEvents,leaf]
    | counted | natural | integer => rfl

theorem projected_write_events (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (origins : Fin jobs.length → Local α) (before : Configuration α jobs.length)
    (dependent : before.Dependencies regions) (projected : before.Projects jobs regions origins)
    (selected : Fin jobs.length) :
    ∃ reference, (origins selected).Advances jobs[selected].backend reference ∧
      reference.pending = (before.locals selected).pending ∧
      (before.locals selected).writeEvents jobs[selected].backend before.memory =
        reference.writeEvents jobs[selected].backend reference.state.mem := by
  obtain ⟨reference,earlier,pending,related⟩ := projected selected
  refine ⟨reference,earlier,pending,?_⟩
  have equal := Local.writeEvents_agree jobs[selected].backend regions reference.pending
    (pending ▸ dependent selected) reference.state (before.focus selected).state related
  simpa only [pending,Configuration.focus,Local.writeEvents] using equal.symm

#axiomsClean Local.writeEvents_agree
#axiomsClean projected_write_events
end
end VeriTile.Triton.FP.Structural.Interleaved
