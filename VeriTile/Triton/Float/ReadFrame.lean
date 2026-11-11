import VeriTile.Triton.Float.ReadDependency

/-! Ordinary stores and discard-result atomic updates preserve their declared
read-only regions. The value written may depend on the actual previous atomic
word; no commutation or equality of destination words is asserted. -/
namespace VeriTile.Triton.FP.Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
variable {α : Type} [Inhabited α]

omit [Inhabited α] in
theorem State.AgreesOn.trans {regions : RegionName → Prop} {first middle last : State α}
    (one : first.AgreesOn regions middle) (two : middle.AgreesOn regions last) : first.AgreesOn regions last :=
  ⟨one.registers.trans two.registers,one.programs.trans two.programs,one.grid.trans two.grid,
    one.undefined.trans two.undefined,fun region member => (one.memory region member).trans (two.memory region member)⟩

omit [Inhabited α] in
theorem State.AgreesOn.fold {ι : Type} (regions : RegionName → Prop) (items : List ι)
    (update : State α → ι → State α) (initial : State α)
    (frame : ∀ state item, (update state item).AgreesOn regions state) :
    (items.foldl update initial).AgreesOn regions initial := by
  induction items generalizing initial with
  | nil => exact State.AgreesOn.refl regions initial
  | cons item rest ih => exact (ih _).trans (frame _ _)

theorem store_region_frame (M : Algebra α) {dtype : TileDType} {shape : TileShape}
    (regions : RegionName → Prop) (region : Region dtype) (outside : ¬ regions (Region.cast region))
    (offset : Op .nat shape) (mask : MaskOpt dtype shape) (values : Values α dtype shape)
    (initial final : State α) (ran : store M (.region region offset) mask values initial = some final) :
    final.AgreesOn regions initial := by
  unfold store at ran
  dsimp only at ran
  cases addresses : evalOp M none offset initial with
  | none => simp [addresses] at ran
  | some offsets =>
      simp only [addresses,Option.map_some,bind,pure,Option.bind_some,Option.bind_eq_some_iff,Option.some.injEq] at ran
      obtain ⟨active,_,same⟩ := ran
      subst final
      apply State.AgreesOn.fold
      intro state lane
      split
      · exact (State.AgreesOn.refl regions state).writeOutside _ _ _ outside
      · exact State.AgreesOn.refl regions state

theorem atomicAdd_region_frame (M : Algebra α) {dtype : TileDType} {shape : TileShape}
    (regions : RegionName → Prop) (region : Region dtype) (outside : ¬ regions (Region.cast region))
    (numeric : NumericDType dtype) (offset : Op .nat shape) (mask : MaskOpt dtype shape) (values : Values α dtype shape)
    (initial final : State α) (ran : atomicAdd M numeric (.region region offset) mask values initial = some final) :
    final.AgreesOn regions initial := by
  unfold atomicAdd at ran
  dsimp only at ran
  cases available : atomicAddition M numeric with
  | none => simp [available] at ran
  | some combine =>
      cases addresses : evalOp M none offset initial with
      | none => simp [available,addresses] at ran
      | some offsets =>
          simp only [available,addresses,Option.map_some,bind,pure,Option.bind_some,Option.bind_eq_some_iff,Option.some.injEq] at ran
          obtain ⟨active,_,same⟩ := ran
          subst final
          apply State.AgreesOn.fold
          intro state lane
          split
          · exact (State.AgreesOn.refl regions state).writeOutside _ _ _ outside
          · exact State.AgreesOn.refl regions state

theorem atomicReduction_region_frame (M : Algebra α) (operation : RMWOp) {dtype : TileDType} {shape : TileShape}
    (regions : RegionName → Prop) (region : Region dtype) (outside : ¬ regions (Region.cast region))
    (offset : Op .nat shape) (mask : MaskOpt dtype shape) (values : Values α dtype shape)
    (initial final : State α) (ran : atomicReduction M operation (.region region offset) mask values initial = some final) :
    final.AgreesOn regions initial := by
  unfold atomicReduction at ran
  split at ran
  · cases dtype <;> try { contradiction }
    all_goals exact atomicAdd_region_frame _ regions region outside _ offset mask values initial final ran
  · simp at ran

#axiomsClean State.AgreesOn.trans
#axiomsClean State.AgreesOn.fold
#axiomsClean store_region_frame
#axiomsClean atomicAdd_region_frame
#axiomsClean atomicReduction_region_frame
end
end VeriTile.Triton.FP.Structural
