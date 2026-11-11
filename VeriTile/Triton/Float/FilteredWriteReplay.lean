import VeriTile.Triton.Float.AtomicWriteStream

/-! Project a concrete memory replay to selected events, provided every
removed event frames the observed cell. This changes neither selected-event
order nor the actual initial memory word. -/
namespace VeriTile.Triton.FP.Structural.MemoryWrite
noncomputable section
variable {α : Type} [Inhabited α]

theorem fold_filter (events : List (MemoryWrite α)) (keep : MemoryWrite α → Bool)
    (region : RegionName) (offset : Nat) (initial : Cell α)
    (framed : ∀ event ∈ events, keep event = false → ∀ old, event.atCell region offset old = old) :
    events.foldl (fun old event => event.atCell region offset old) initial =
      (events.filter keep).foldl (fun old event => event.atCell region offset old) initial := by
  induction events generalizing initial with
  | nil => rfl
  | cons event rest ih =>
      have tail : ∀ other ∈ rest, keep other = false → ∀ old, other.atCell region offset old = old := by
        intro other member; exact framed other (by simp [member])
      cases selected : keep event
      · simp only [List.foldl_cons,List.filter_cons,selected,ite_false,framed event (by simp) selected]
        exact ih initial tail
      · simp only [List.foldl_cons,List.filter_cons,selected,ite_true]
        exact ih (event.atCell region offset initial) tail

theorem lanes_frame {ι : Type} (indices : List ι) (active : ι → Bool) (make : ι → MemoryWrite α)
    (region : RegionName) (offset : Nat)
    (framed : ∀ i ∈ indices, active i = true → ∀ old, (make i).atCell region offset old = old)
    (event : MemoryWrite α) (member : event ∈ lanes indices active make) (old : Cell α) :
    event.atCell region offset old = old := by
  obtain ⟨i,inside,generated⟩ := List.mem_filterMap.mp member
  cases selected : active i
  · simp [selected] at generated
  · have equal : make i = event := by simpa [selected] using generated
    subst event
    exact framed i inside selected old

#axiomsClean fold_filter
#axiomsClean lanes_frame
end
end VeriTile.Triton.FP.Structural.MemoryWrite
