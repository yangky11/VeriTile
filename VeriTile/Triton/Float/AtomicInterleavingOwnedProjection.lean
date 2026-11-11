import VeriTile.Triton.Float.AtomicInterleavingCellAgreement
import VeriTile.Triton.Float.AtomicInterleavingPermission
import VeriTile.Triton.Float.AtomicInterleavingProjection

/-! Per-cell source projection under exclusive ordinary/atomic write
permissions. Shared atomic destinations need not be assigned an owner. Every
permission is an obligation over actual source prefixes, not a native callback. -/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

def Configuration.OwnedProjects (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (origins : Fin jobs.length → Local α) (owned : Fin jobs.length → RegionName → Nat → Prop)
    (state : Configuration α jobs.length) : Prop :=
  ∀ i, ∃ reference : Local α,
    (origins i).Advances jobs[i].backend reference ∧
    reference.pending = (state.focus i).pending ∧
    reference.state.AgreesOn regions (state.focus i).state ∧
    reference.state.CellsAgree (owned i) (state.focus i).state

theorem tick_owned_projects (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (origins : Fin jobs.length → Local α) (owned ordinary atomic : Fin jobs.length → RegionName → Nat → Prop)
    (permissions : ∀ i reference, (origins i).Advances jobs[i].backend reference →
      reference.Permitted jobs[i].backend (ordinary i) (atomic i) reference.state.mem)
    (exclusive : ∀ writer reader, writer ≠ reader → ∀ region offset, owned reader region offset →
      ¬ ordinary writer region offset ∧ ¬ atomic writer region offset)
    (selected : Fin jobs.length) (before after : Configuration α jobs.length)
    (confined : before.ReadOnly regions) (dependent : before.Dependencies regions)
    (projected : before.OwnedProjects jobs regions origins owned)
    (ran : tick jobs selected before = some after) :
    after.OwnedProjects jobs regions origins owned := by
  obtain ⟨next,advanced,returned⟩ := Option.bind_eq_some_iff.mp ran
  have equal := Option.some.inj returned
  subst after
  obtain ⟨selectedReference,selectedEarlier,selectedPending,selectedRelated,_⟩ := projected selected
  have selectedPermitted := (Local.permitted_agrees jobs[selected].backend regions (ordinary selected) (atomic selected)
    selectedReference.pending (selectedPending ▸ dependent selected) selectedReference.state
    (before.focus selected).state selectedRelated).mp (permissions selected selectedReference selectedEarlier)
  have actualPermitted : (before.locals selected).Permitted jobs[selected].backend
      (ordinary selected) (atomic selected) before.memory := by
    simpa only [selectedPending,Configuration.focus,Local.Permitted] using selectedPermitted
  have cellFrame := Local.tick_permission_frame jobs[selected].backend (ordinary selected) (atomic selected)
    (before.locals selected) next before.memory actualPermitted advanced
  have framed := (Local.tick_readOnly jobs[selected].backend regions
    (before.locals selected) next before.memory (confined selected) advanced).2
  intro i
  obtain ⟨reference,earlier,pending,related,equalCells⟩ := projected i
  by_cases selectedHere : i = selected
  · subst i
    have advanced' : (Local.mk reference.pending (before.focus selected).state).tick
        jobs[selected].backend (before.focus selected).state.mem = some next := by
      simpa only [pending,Configuration.focus,Local.tick] using advanced
    obtain ⟨other,executed,control,same⟩ := tick_agrees jobs[selected].backend regions reference.pending
      (pending ▸ confined selected) (pending ▸ dependent selected)
      (before.focus selected).state reference.state related.symm next advanced'
    have cells := tick_cells_agree jobs[selected].backend regions (owned selected) reference.pending
      (pending ▸ dependent selected) (before.focus selected).state reference.state next other
      related.symm equalCells.symm advanced' executed
    refine ⟨other,earlier.tail executed,?_,?_,?_⟩
    · simpa [Configuration.focus] using control.symm
    · simpa [Configuration.focus] using same.symm
    · simpa [Configuration.focus] using cells.symm
  · refine ⟨reference,earlier,?_,?_,?_⟩
    · simpa [Configuration.focus,Function.update,selectedHere] using pending
    · refine ⟨?_,?_,?_,?_,?_⟩
      · simpa [Configuration.focus,Function.update,selectedHere] using related.registers
      · simpa [Configuration.focus,Function.update,selectedHere] using related.programs
      · simpa [Configuration.focus,Function.update,selectedHere] using related.grid
      · simpa [Configuration.focus,Function.update,selectedHere] using related.undefined
      · intro region member
        exact (related.memory region member).trans (framed region member).symm
    · intro region offset member
      obtain ⟨ordinaryOutside,atomicOutside⟩ := exclusive selected i (Ne.symm selectedHere) region offset member
      exact (equalCells region offset member).trans (cellFrame region offset ordinaryOutside atomicOutside).symm

theorem run_owned_projects (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (origins : Fin jobs.length → Local α) (owned ordinary atomic : Fin jobs.length → RegionName → Nat → Prop)
    (permissions : ∀ i reference, (origins i).Advances jobs[i].backend reference →
      reference.Permitted jobs[i].backend (ordinary i) (atomic i) reference.state.mem)
    (exclusive : ∀ writer reader, writer ≠ reader → ∀ region offset, owned reader region offset →
      ¬ ordinary writer region offset ∧ ¬ atomic writer region offset)
    (schedule : List (Fin jobs.length)) (before after : Configuration α jobs.length)
    (confined : before.ReadOnly regions) (dependent : before.Dependencies regions)
    (projected : before.OwnedProjects jobs regions origins owned)
    (ran : run jobs schedule before = some after) :
    after.OwnedProjects jobs regions origins owned := by
  induction schedule generalizing before with
  | nil => simp only [run,Option.some.injEq] at ran; subst after; exact projected
  | cons selected rest ih =>
      obtain ⟨next,advanced,remaining⟩ := Option.bind_eq_some_iff.mp ran
      exact ih next (tick_readOnly jobs regions selected before next confined advanced).1
        (tick_dependencies jobs regions selected before next dependent advanced)
        (tick_owned_projects jobs regions origins owned ordinary atomic permissions exclusive selected before next
          confined dependent projected advanced) remaining

theorem initial_owned_projects (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (owned : Fin jobs.length → RegionName → Nat → Prop) (state : State α) :
    (initial jobs state).OwnedProjects jobs regions (initial jobs state).locals owned := by
  intro i
  refine ⟨(initial jobs state).locals i,Relation.ReflTransGen.refl,rfl,?_,?_⟩
  · refine ⟨rfl,rfl,rfl,rfl,?_⟩
    intro region member
    simp [initial,Configuration.focus]
  · intro region offset member
    simp [initial,Configuration.focus]

/-- Every owned final cell equals the actual isolated source execution of its
owner. Atomic words shared by multiple workers remain outside this conclusion. -/
theorem Run.project_owned (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (owned ordinary atomic : Fin jobs.length → RegionName → Nat → Prop)
    (before after : State α) (executed : Run jobs before after)
    (confined : ∀ i : Fin jobs.length, readOnlyBody regions jobs[i].kernel.surfaceBody)
    (dependent : ∀ i : Fin jobs.length, bodyDependencies regions jobs[i].kernel.surfaceBody)
    (permissions : ∀ i reference, ((initial jobs before).locals i).Advances jobs[i].backend reference →
      reference.Permitted jobs[i].backend (ordinary i) (atomic i) reference.state.mem)
    (exclusive : ∀ writer reader, writer ≠ reader → ∀ region offset, owned reader region offset →
      ¬ ordinary writer region offset ∧ ¬ atomic writer region offset)
    (i : Fin jobs.length) :
    ∃ isolated, jobs[i].run before = some isolated ∧
      ∀ region offset, owned i region offset → after.mem region offset = isolated.mem region offset := by
  obtain ⟨reference,advanced,pending,_,cells⟩ := run_owned_projects jobs regions
    (initial jobs before).locals owned ordinary atomic permissions exclusive executed.schedule
    (initial jobs before) executed.result (initial_readOnly jobs regions before confined)
    (initial_dependencies jobs regions before dependent) (initial_owned_projects jobs regions owned before)
    executed.executed i
  have completed : reference.pending = [] := pending.trans (executed.complete i)
  have denoted := advanced.denotes jobs[i].backend
  rw [completed,evaluate] at denoted
  refine ⟨reference.state,?_,?_⟩
  · change exec jobs[i].backend jobs[i].kernel (jobs[i].initial before) = some reference.state
    change evaluate jobs[i].backend
      (match jobs[i].kernel with | .mk _ _ body => commands body) (jobs[i].initial before) = _ at denoted
    cases kernel : jobs[i].kernel
    simp only [kernel,exec] at *
    exact (evaluate_commands _ _ _).symm.trans denoted
  · intro region offset member
    rw [executed.readback]
    exact (cells region offset member).symm

#axiomsClean tick_owned_projects
#axiomsClean run_owned_projects
#axiomsClean initial_owned_projects
#axiomsClean Run.project_owned
end
end VeriTile.Triton.FP.Structural.Interleaved
