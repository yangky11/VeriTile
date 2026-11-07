import VeriTile.Triton.Source.Proof

/-! Readback from a masked scatter after pushing a scalar observation through
memory. Inactive lanes may share addresses with active lanes. The only required
ownership fact is that every selected write stores the desired value. -/
namespace VeriTile.Triton

/-- `some`-form of addition for reduction carriers. An explicit `WithBot`
addition instance prevents `Option` typeclass inference from changing the sum. -/
theorem withBot_add_some {α : Type} [Add α] (a b : α) :
    @HAdd.hAdd (WithBot α) (WithBot α) (WithBot α) _ (some a) (some b) =
      some (a + b) := rfl

private theorem foldl_select_preserves {α β : Type} (items : List α)
    (selected : α → Prop) [DecidablePred selected] (value : α → β) (expected : β)
    (values : ∀ i ∈ items, selected i → value i = expected) :
    items.foldl (fun previous i => if selected i then value i else previous) expected = expected := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      rw [List.foldl_cons]
      have ht : ∀ i ∈ tail, selected i → value i = expected :=
        fun i hi => values i (List.mem_cons_of_mem _ hi)
      by_cases hs : selected head
      · rw [if_pos hs, values head List.mem_cons_self hs]
        exact ih ht
      · rw [if_neg hs]
        exact ih ht

/-- Every selected writer agrees, and at least one writer is selected. This
allows overlapping *inactive* padded lanes without weakening active ownership. -/
theorem foldl_select_readback {α β : Type} (items : List α)
    (selected : α → Prop) [DecidablePred selected] (value : α → β) (expected initial : β)
    (values : ∀ i ∈ items, selected i → value i = expected)
    (written : ∃ i ∈ items, selected i) :
    items.foldl (fun previous i => if selected i then value i else previous) initial = expected := by
  induction items generalizing initial with
  | nil => simpa using written
  | cons head tail ih =>
      rw [List.foldl_cons]
      have ht : ∀ i ∈ tail, selected i → value i = expected :=
        fun i hi => values i (List.mem_cons_of_mem _ hi)
      by_cases hs : selected head
      · rw [if_pos hs, values head List.mem_cons_self hs]
        exact foldl_select_preserves tail selected value expected ht
      · rw [if_neg hs]
        apply ih initial ht
        obtain ⟨i, hi, hselected⟩ := written
        rcases List.mem_cons.mp hi with rfl | hi
        · exact False.elim (hs hselected)
        · exact ⟨i, hi, hselected⟩

end VeriTile.Triton
