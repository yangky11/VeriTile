import VeriTile.Triton.Float.AtomicInterleavingPermissionPrefix

/-! Source trace permissions frame cells outside every worker's permitted
writes across arbitrary actual schedules, including padding inside destinations. -/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

theorem projected_tick_permitted (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (origins : Fin jobs.length → Local α) (ordinary atomic : Fin jobs.length → RegionName → Nat → Prop)
    (permissions : ∀ i reference, (origins i).Advances jobs[i].backend reference →
      reference.Permitted jobs[i].backend (ordinary i) (atomic i) reference.state.mem)
    (before : Configuration α jobs.length) (dependent : before.Dependencies regions)
    (projected : before.Projects jobs regions origins) (selected : Fin jobs.length) :
    (before.locals selected).Permitted jobs[selected].backend (ordinary selected) (atomic selected) before.memory := by
  obtain ⟨reference,earlier,pending,related⟩ := projected selected
  have allowed := (Local.permitted_agrees jobs[selected].backend regions (ordinary selected) (atomic selected)
    reference.pending (pending ▸ dependent selected) reference.state (before.focus selected).state related).mp
      (permissions selected reference earlier)
  simpa only [pending,Configuration.focus,Local.Permitted] using allowed

theorem run_permission_frame (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (origins : Fin jobs.length → Local α) (ordinary atomic : Fin jobs.length → RegionName → Nat → Prop)
    (permissions : ∀ i reference, (origins i).Advances jobs[i].backend reference →
      reference.Permitted jobs[i].backend (ordinary i) (atomic i) reference.state.mem)
    (schedule : List (Fin jobs.length)) (before after : Configuration α jobs.length)
    (confined : before.ReadOnly regions) (dependent : before.Dependencies regions)
    (projected : before.Projects jobs regions origins)
    (ran : run jobs schedule before = some after)
    (region : RegionName) (offset : Nat)
    (outside : ∀ i, ¬ ordinary i region offset ∧ ¬ atomic i region offset) :
    after.memory region offset = before.memory region offset := by
  induction schedule generalizing before with
  | nil => simp only [run,Option.some.injEq] at ran; subst after; rfl
  | cons selected rest ih =>
      obtain ⟨next,advanced,remaining⟩ := Option.bind_eq_some_iff.mp ran
      have restFrame := ih next (tick_readOnly jobs regions selected before next confined advanced).1
        (tick_dependencies jobs regions selected before next dependent advanced)
        (tick_projects jobs regions origins selected before next confined dependent projected advanced) remaining
      rw [restFrame]
      have permitted := projected_tick_permitted jobs regions origins ordinary atomic permissions before dependent projected selected
      obtain ⟨thread,ticked,returned⟩ := Option.bind_eq_some_iff.mp advanced
      have equal := Option.some.inj returned
      subst next
      exact Local.tick_permission_frame jobs[selected].backend (ordinary selected) (atomic selected)
        (before.locals selected) thread before.memory permitted ticked region offset (outside selected).1 (outside selected).2

theorem Run.permission_frame (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (ordinary atomic : Fin jobs.length → RegionName → Nat → Prop)
    (before after : State α) (executed : Run jobs before after)
    (confined : ∀ i : Fin jobs.length, readOnlyBody regions jobs[i].kernel.surfaceBody)
    (dependent : ∀ i : Fin jobs.length, bodyDependencies regions jobs[i].kernel.surfaceBody)
    (permissions : ∀ i : Fin jobs.length, Permission.trace jobs[i].backend (ordinary i) (atomic i)
      jobs[i].kernel.surfaceBody (jobs[i].initial before))
    (region : RegionName) (offset : Nat) (outside : ∀ i, ¬ ordinary i region offset ∧ ¬ atomic i region offset) :
    after.mem region offset = before.mem region offset := by
  rw [executed.readback]
  apply run_permission_frame jobs regions (initial jobs before).locals ordinary atomic ?_ executed.schedule
    (initial jobs before) executed.result (initial_readOnly jobs regions before confined)
    (initial_dependencies jobs regions before dependent) (initial_projects jobs regions before) executed.executed region offset outside
  intro i reference advanced
  apply source_prefix_permitted jobs[i].backend (ordinary i) (atomic i)
    jobs[i].kernel.surfaceBody (jobs[i].initial before) reference (permissions i)
  cases kernel : jobs[i].kernel
  simpa only [initial,kernel,ComputeKernel.surfaceBody] using advanced

#axiomsClean projected_tick_permitted
#axiomsClean run_permission_frame
#axiomsClean Run.permission_frame
end
end VeriTile.Triton.FP.Structural.Interleaved
