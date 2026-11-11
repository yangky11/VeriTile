import VeriTile.Triton.Float.CellWriteSemantics

/-! Corresponding source writes preserve arbitrary cell agreement. Atomic
updates compare the actual previous word at owned cells, without commuting any
updates or assuming an algebraic law of the reduction backend. -/
namespace VeriTile.Triton.FP.Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

theorem store_cells_agree (M : Algebra α) (regions : RegionName → Prop)
    (cells : RegionName → Nat → Prop) (access : MemAccess dtype shape) (mask : MaskOpt dtype shape)
    (addressDependency : accessReads regions access) (maskDependency : maskReads regions mask)
    (values : Values α dtype shape) (first second final other : State α)
    (same : first.AgreesOn regions second) (equalCells : first.CellsAgree cells second)
    (one : store M access mask values first = some final)
    (two : store M access mask values second = some other) : final.CellsAgree cells other := by
  cases access with
  | ptr | blockPtr => simp [accessReads] at addressDependency
  | region region offset =>
      rw [store_region_eq,Reads.eval_eq addressDependency M none first second same,
        writeMask_eq M maskDependency first second same] at one
      rw [store_region_eq] at two
      cases addresses : evalOp M none offset second <;> cases active : writeMask M mask second <;>
        simp only [addresses,active,Option.bind_none,Option.bind_some,Option.some.injEq] at one two
      all_goals try contradiction
      subst final other
      apply State.CellsAgree.fold cells _ _ _ first second equalCells
      intro a b lane related
      split
      · exact related.write _ _ _ _ (fun _ => rfl)
      · exact related

theorem atomicAdd_cells_agree (M : Algebra α) (regions : RegionName → Prop)
    (cells : RegionName → Nat → Prop) (numeric : NumericDType dtype)
    (access : MemAccess dtype shape) (mask : MaskOpt dtype shape)
    (addressDependency : accessReads regions access) (maskDependency : maskReads regions mask)
    (values : Values α dtype shape) (first second final other : State α)
    (same : first.AgreesOn regions second) (equalCells : first.CellsAgree cells second)
    (one : atomicAdd M numeric access mask values first = some final)
    (two : atomicAdd M numeric access mask values second = some other) : final.CellsAgree cells other := by
  cases access with
  | ptr | blockPtr => simp [accessReads] at addressDependency
  | region region offset =>
      rw [atomicAdd_region_eq,Reads.eval_eq addressDependency M none first second same,
        writeMask_eq M maskDependency first second same] at one
      rw [atomicAdd_region_eq] at two
      cases available : atomicAddition M numeric <;>
        cases addresses : evalOp M none offset second <;> cases active : writeMask M mask second <;>
          simp only [available,addresses,active,Option.bind_none,Option.bind_some,Option.some.injEq] at one two
      all_goals try contradiction
      subst final other
      apply State.CellsAgree.fold cells _ _ _ first second equalCells
      intro a b lane related
      split
      · apply related.write
        intro owned
        rw [related _ _ owned]
      · exact related

theorem atomicReduction_cells_agree (M : Algebra α) (operation : RMWOp) (regions : RegionName → Prop)
    (cells : RegionName → Nat → Prop) (access : MemAccess dtype shape) (mask : MaskOpt dtype shape)
    (addressDependency : accessReads regions access) (maskDependency : maskReads regions mask)
    (values : Values α dtype shape) (first second final other : State α)
    (same : first.AgreesOn regions second) (equalCells : first.CellsAgree cells second)
    (one : atomicReduction M operation access mask values first = some final)
    (two : atomicReduction M operation access mask values second = some other) : final.CellsAgree cells other := by
  unfold atomicReduction at one two
  split at one
  · rename_i admitted
    simp only [admitted,ite_true] at two
    cases dtype <;> try contradiction
    all_goals
      exact atomicAdd_cells_agree _ regions cells _ access mask addressDependency maskDependency
        values first second final other same equalCells one two
  · contradiction

#axiomsClean atomicReduction_cells_agree
#axiomsClean store_cells_agree
#axiomsClean atomicAdd_cells_agree
end
end VeriTile.Triton.FP.Structural
