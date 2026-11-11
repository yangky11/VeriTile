import VeriTile.Triton.Float.CellWriteSemantics

/-! Compositional write permissions cover arbitrary, noncontiguous cell sets.
The permitted addresses come from the actual source offset and mask evaluators. -/
namespace VeriTile.Triton.FP.Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

def writePermitted (M : Algebra α) (allowed : RegionName → Nat → Prop)
    (access : MemAccess dtype shape) (mask : MaskOpt dtype shape) (state : State α) : Prop :=
  match access with
  | .region region offset => ∀ offsets, evalOp M none offset state = some offsets →
      ∀ lane, Safety.maskActive M none state mask lane → allowed (Region.cast region) (offsets lane)
  | _ => False

theorem writePermitted_iff (M : Algebra α) (regions : RegionName → Prop) (allowed : RegionName → Nat → Prop)
    (access : MemAccess dtype shape) (mask : MaskOpt dtype shape)
    (addressDependency : accessReads regions access) (maskDependency : maskReads regions mask)
    (first second : State α) (same : first.AgreesOn regions second) :
    writePermitted M allowed access mask first ↔ writePermitted M allowed access mask second := by
  cases access with
  | ptr | blockPtr => rfl
  | region region offset =>
      have addresses := Reads.eval_eq addressDependency M none first second same
      cases mask with
      | none => simp only [writePermitted,Safety.maskActive,addresses]
      | mask condition =>
          simp only [writePermitted,Safety.maskActive,addresses,
            Reads.eval_eq maskDependency M none first second same]
      | maskOther condition other =>
          simp only [writePermitted,Safety.maskActive,addresses,
            Reads.eval_eq maskDependency.1 M none first second same]

theorem store_permission_frame (M : Algebra α) (allowed : RegionName → Nat → Prop)
    (access : MemAccess dtype shape) (mask : MaskOpt dtype shape) (values : Values α dtype shape)
    (initial final : State α) (permitted : writePermitted M allowed access mask initial)
    (ran : store M access mask values initial = some final) :
    final.CellsAgree (fun region offset => ¬ allowed region offset) initial := by
  cases access with
  | ptr | blockPtr => simp [writePermitted] at permitted
  | region region offset =>
      rw [store_region_eq] at ran
      cases addresses : evalOp M none offset initial with
      | none => simp [addresses] at ran
      | some offsets =>
          cases selected : writeMask M mask initial with
          | none => simp [addresses,selected] at ran
          | some active =>
              simp only [addresses,selected,Option.bind_some,Option.some.injEq] at ran
              subst final
              apply State.CellsAgree.fold_frame
              intro state lane
              split
              · rename_i enabled
                apply (State.CellsAgree.refl _ state).writeOutside
                exact not_not.mpr (permitted offsets addresses lane
                  (writeMask_active M mask initial active selected lane enabled))
              · exact State.CellsAgree.refl _ state

theorem atomicAdd_permission_frame (M : Algebra α) (allowed : RegionName → Nat → Prop)
    (numeric : NumericDType dtype) (access : MemAccess dtype shape) (mask : MaskOpt dtype shape)
    (values : Values α dtype shape) (initial final : State α)
    (permitted : writePermitted M allowed access mask initial)
    (ran : atomicAdd M numeric access mask values initial = some final) :
    final.CellsAgree (fun region offset => ¬ allowed region offset) initial := by
  cases access with
  | ptr | blockPtr => simp [writePermitted] at permitted
  | region region offset =>
      rw [atomicAdd_region_eq] at ran
      cases available : atomicAddition M numeric with
      | none => simp [available] at ran
      | some combine =>
        cases addresses : evalOp M none offset initial with
        | none => simp [available,addresses] at ran
        | some offsets =>
            cases selected : writeMask M mask initial with
            | none => simp [available,addresses,selected] at ran
            | some active =>
                simp only [available,addresses,selected,Option.bind_some,Option.some.injEq] at ran
                subst final
                apply State.CellsAgree.fold_frame
                intro state lane
                split
                · rename_i enabled
                  apply (State.CellsAgree.refl _ state).writeOutside
                  exact not_not.mpr (permitted offsets addresses lane
                    (writeMask_active M mask initial active selected lane enabled))
                · exact State.CellsAgree.refl _ state

theorem atomicReduction_permission_frame (M : Algebra α) (operation : RMWOp)
    (allowed : RegionName → Nat → Prop) (access : MemAccess dtype shape) (mask : MaskOpt dtype shape)
    (values : Values α dtype shape) (initial final : State α)
    (permitted : writePermitted { M with atomicAdd := M.atomicReduce operation } allowed access mask initial)
    (ran : atomicReduction M operation access mask values initial = some final) :
    final.CellsAgree (fun region offset => ¬ allowed region offset) initial := by
  unfold atomicReduction at ran
  split at ran
  · cases dtype <;> try contradiction
    all_goals exact atomicAdd_permission_frame _ allowed _ access mask values initial final permitted ran
  · contradiction

#axiomsClean atomicReduction_permission_frame
#axiomsClean writePermitted_iff
#axiomsClean store_permission_frame
#axiomsClean atomicAdd_permission_frame
end
end VeriTile.Triton.FP.Structural
