import VeriTile.Triton.Float.AtomicInterleavingSafeTick
import VeriTile.Triton.Float.AtomicInterleavingProjection
import VeriTile.Triton.Float.AtomicInterleavingSafetyDependency

/-! Source trace safety transfers to arbitrary successful statement schedules
through the proved worker projection and structural read dependencies. -/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

theorem Local.Advances.traceSafe (M : Algebra α) (bounds : RegionName → Nat)
    {before after : Local α} (advanced : before.Advances M after)
    (safe : evaluateSafe M bounds before.pending before.state) :
    evaluateSafe M bounds after.pending after.state := by
  induction advanced with
  | refl => exact safe
  | tail _ tick ih => exact (tick_traceSafe M bounds _ _ _ ih tick).2

theorem projected_tick_safe (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (origins : Fin jobs.length → Local α) (bounds : RegionName → Nat)
    (originSafe : ∀ i, evaluateSafe jobs[i].backend bounds (origins i).pending (origins i).state)
    (selected : Fin jobs.length) (before after : Configuration α jobs.length)
    (confined : before.ReadOnly regions) (dependent : before.Dependencies regions)
    (projected : before.Projects jobs regions origins)
    (ran : tick jobs selected before = some after) :
    (before.locals selected).Safe jobs[selected].backend bounds before.memory := by
  obtain ⟨next,advanced,_⟩ := Option.bind_eq_some_iff.mp ran
  obtain ⟨reference,earlier,pending,related⟩ := projected selected
  have advanced' : (Local.mk reference.pending (before.focus selected).state).tick
      jobs[selected].backend (before.focus selected).state.mem = some next := by
    simpa only [pending,Configuration.focus,Local.tick] using advanced
  obtain ⟨other,executed,_,_⟩ := tick_agrees jobs[selected].backend regions reference.pending
    (pending ▸ confined selected) (pending ▸ dependent selected)
    (before.focus selected).state reference.state related.symm next advanced'
  have referenceSafe := (tick_traceSafe jobs[selected].backend bounds _ _ _
    (earlier.traceSafe jobs[selected].backend bounds (originSafe selected)) executed).1
  have focusedSafe := (Local.safe_agrees jobs[selected].backend regions reference.pending
    (pending ▸ dependent selected) bounds reference.state (before.focus selected).state related).mp referenceSafe
  simpa only [pending,Configuration.focus,Local.Safe] using focusedSafe

theorem run_safe_of_projection (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (origins : Fin jobs.length → Local α) (bounds : RegionName → Nat)
    (originSafe : ∀ i, evaluateSafe jobs[i].backend bounds (origins i).pending (origins i).state)
    (schedule : List (Fin jobs.length)) (before after : Configuration α jobs.length)
    (confined : before.ReadOnly regions) (dependent : before.Dependencies regions)
    (projected : before.Projects jobs regions origins)
    (ran : run jobs schedule before = some after) : Safe jobs bounds schedule before := by
  induction schedule generalizing before with
  | nil => trivial
  | cons selected rest ih =>
      obtain ⟨next,advanced,remaining⟩ := Option.bind_eq_some_iff.mp ran
      refine ⟨projected_tick_safe jobs regions origins bounds originSafe selected before next
        confined dependent projected advanced,?_⟩
      intro other otherRun
      have equal : other = next := Option.some.inj (otherRun.symm.trans advanced)
      subst other
      exact ih next (tick_readOnly jobs regions selected before next confined advanced).1
        (tick_dependencies jobs regions selected before next dependent advanced)
        (tick_projects jobs regions origins selected before next confined dependent projected advanced) remaining

/-- The safety premise is the existing sequential source predicate, not a new
whole-kernel execution assumption. The actual successful schedule is arbitrary. -/
theorem run_safe (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (bounds : RegionName → Nat) (before : State α) (schedule : List (Fin jobs.length))
    (after : Configuration α jobs.length)
    (confined : ∀ i : Fin jobs.length, readOnlyBody regions jobs[i].kernel.surfaceBody)
    (dependent : ∀ i : Fin jobs.length, bodyDependencies regions jobs[i].kernel.surfaceBody)
    (sourceSafe : ∀ i : Fin jobs.length, jobs[i].Safe bounds before)
    (ran : run jobs schedule (initial jobs before) = some after) :
    Safe jobs bounds schedule (initial jobs before) := by
  apply run_safe_of_projection jobs regions (initial jobs before).locals bounds ?_ schedule
    (initial jobs before) after (initial_readOnly jobs regions before confined)
    (initial_dependencies jobs regions before dependent) (initial_projects jobs regions before) ran
  intro i
  have safe := sourceSafe i
  change TraceSafe jobs[i].backend bounds jobs[i].kernel (jobs[i].initial before) at safe
  change evaluateSafe jobs[i].backend bounds
    (match jobs[i].kernel with | .mk _ _ body => commands body) (jobs[i].initial before)
  cases kernel : jobs[i].kernel
  simp only [kernel,TraceSafe] at safe
  exact (evaluateSafe_commands _ _ _ _).mpr safe

#axiomsClean Local.Advances.traceSafe
#axiomsClean projected_tick_safe
#axiomsClean run_safe_of_projection
#axiomsClean run_safe
end
end VeriTile.Triton.FP.Structural.Interleaved
