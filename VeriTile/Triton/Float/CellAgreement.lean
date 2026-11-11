import VeriTile.Triton.Float.ReadDependency

/-! Pointwise memory agreement for noncontiguous ownership sets. Distinct
workers may own disjoint cells of the same allocation. -/
namespace VeriTile.Triton.FP.Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev State.CellsAgree {α : Type} (cells : RegionName → Nat → Prop) (first second : State α) : Prop :=
  ∀ region offset, cells region offset → first.mem region offset = second.mem region offset

theorem State.CellsAgree.refl {α : Type} (cells : RegionName → Nat → Prop) (state : State α) :
    state.CellsAgree cells state := fun _ _ _ => rfl

theorem State.CellsAgree.symm {α : Type} {cells : RegionName → Nat → Prop} {first second : State α}
    (same : first.CellsAgree cells second) : second.CellsAgree cells first := fun r o member => (same r o member).symm

theorem State.CellsAgree.trans {α : Type} {cells : RegionName → Nat → Prop} {first middle last : State α}
    (one : first.CellsAgree cells middle) (two : middle.CellsAgree cells last) : first.CellsAgree cells last :=
  fun r o member => (one r o member).trans (two r o member)

theorem State.CellsAgree.write {α : Type} {cells : RegionName → Nat → Prop} {first second : State α}
    (same : first.CellsAgree cells second) (region : RegionName) (offset : Nat) (value other : Cell α)
    (equal : cells region offset → value = other) :
    (first.write region offset value).CellsAgree cells (second.write region offset other) := by
  intro r o member
  by_cases target : r = region ∧ o = offset
  · rcases target with ⟨rfl,rfl⟩
    simpa only [State.write_same] using equal member
  · have distinct : r ≠ region ∨ o ≠ offset := not_and_or.mp target
    rw [State.write_other _ _ _ _ _ _ distinct,State.write_other _ _ _ _ _ _ distinct]
    exact same r o member

theorem State.CellsAgree.writeOutside {α : Type} {cells : RegionName → Nat → Prop} {first second : State α}
    (same : first.CellsAgree cells second) (region : RegionName) (offset : Nat) (value : Cell α)
    (outside : ¬ cells region offset) : (first.write region offset value).CellsAgree cells second := by
  intro r o member
  have distinct : r ≠ region ∨ o ≠ offset := by
    by_contra h
    push Not at h
    exact outside (h.1 ▸ h.2 ▸ member)
  rw [State.write_other _ _ _ _ _ _ distinct]
  exact same r o member

theorem State.CellsAgree.fold {α ι : Type} (cells : RegionName → Nat → Prop) (items : List ι)
    (update : State α → ι → State α) (other : State α → ι → State α)
    (first second : State α) (same : first.CellsAgree cells second)
    (preserves : ∀ a b item, a.CellsAgree cells b → (update a item).CellsAgree cells (other b item)) :
    (items.foldl update first).CellsAgree cells (items.foldl other second) := by
  induction items generalizing first second with
  | nil => exact same
  | cons item rest ih => exact ih _ _ (preserves _ _ _ same)

theorem State.CellsAgree.fold_frame {α ι : Type} (cells : RegionName → Nat → Prop) (items : List ι)
    (update : State α → ι → State α) (initial : State α)
    (preserves : ∀ state item, (update state item).CellsAgree cells state) :
    (items.foldl update initial).CellsAgree cells initial := by
  induction items generalizing initial with
  | nil => exact State.CellsAgree.refl cells initial
  | cons item rest ih => exact (ih _).trans (preserves _ _)

#axiomsClean State.CellsAgree.refl
#axiomsClean State.CellsAgree.symm
#axiomsClean State.CellsAgree.trans
#axiomsClean State.CellsAgree.write
#axiomsClean State.CellsAgree.writeOutside
#axiomsClean State.CellsAgree.fold
#axiomsClean State.CellsAgree.fold_frame
end
end VeriTile.Triton.FP.Structural
