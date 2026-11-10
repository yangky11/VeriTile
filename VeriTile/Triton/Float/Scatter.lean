import VeriTile.Triton.Float.Structural
import VeriTile.Meta.StatementAudit

/-! Memory and readback rules for typed scatters. Padded tiles need injectivity
only on active lanes: inactive addresses may alias or exceed allocation bounds.
These rules preserve raw typed cells and assume no floating arithmetic laws. -/
namespace VeriTile.Triton.FP.Structural.State

theorem write_memory_congr {α : Type} (first second : State α)
    (region : RegionName) (offset : Nat) (value : Cell α) (same : first.mem = second.mem) :
    (first.write region offset value).mem = (second.write region offset value).mem := by
  funext r o
  simp only [State.write,same]

@[simp] theorem masked_scatter_regs {α ι : Type} (region : RegionName) (offset : ι → Nat)
    (value : ι → Cell α) (active : ι → Prop) [DecidablePred active]
    (indices : List ι) (initial : State α) :
    (indices.foldl (fun state i => if active i then state.write region (offset i) (value i)
      else state) initial).regs = initial.regs := by
  rw [masked_scatter_eq_filter, scatter_regs]

theorem scatter_memory_congr {α ι : Type} (region : RegionName) (offset : ι → Nat)
    (value : ι → Cell α) (indices : List ι) (first second : State α)
    (same : first.mem = second.mem) :
    (indices.foldl (fun state i => state.write region (offset i) (value i)) first).mem =
      (indices.foldl (fun state i => state.write region (offset i) (value i)) second).mem := by
  induction indices generalizing first second with
  | nil => exact same
  | cons i rest ih =>
    apply ih
    funext r o
    simp [State.write, same]

theorem masked_scatter_memory_congr {α ι : Type} (region : RegionName) (offset : ι → Nat)
    (value : ι → Cell α) (active : ι → Prop) [DecidablePred active]
    (indices : List ι) (first second : State α) (same : first.mem = second.mem) :
    (indices.foldl (fun state i => if active i then state.write region (offset i) (value i)
      else state) first).mem =
    (indices.foldl (fun state i => if active i then state.write region (offset i) (value i)
      else state) second).mem := by
  rw [masked_scatter_eq_filter, masked_scatter_eq_filter]
  exact scatter_memory_congr _ _ _ _ _ _ same

theorem scatter_readback_list_on {α ι : Type} (region : RegionName) (offset : ι → Nat)
    (value : ι → Cell α) (indices : List ι) (initial : State α) (selected : ι)
    (nodup : indices.Nodup) (member : selected ∈ indices)
    (injective : ∀ i ∈ indices, ∀ j ∈ indices, offset i = offset j → i = j) :
    (indices.foldl (fun state i => state.write region (offset i) (value i)) initial).mem
      region (offset selected) = value selected := by
  obtain ⟨before, after, split⟩ := List.append_of_mem member
  have absent := nodup
  rw [split, List.nodup_append, List.nodup_cons] at absent
  rw [split, List.foldl_append, List.foldl_cons, scatter_frame]
  · exact write_same _ _ _ _
  · right
    intro i hi same
    have member' : i ∈ indices := by simp [split, hi]
    exact absent.2.1.1 ((injective selected member i member' same) ▸ hi)

theorem masked_scatter_readback_on {α : Type} {shape : TileShape}
    (region : RegionName) (offset : TileIndex shape → Nat) (value : TileIndex shape → Cell α)
    (active : TileIndex shape → Prop) [DecidablePred active] (initial : State α)
    (selected : TileIndex shape) (hit : active selected)
    (injective : ∀ i j, active i → active j → offset i = offset j → i = j) :
    ((TileShape.allIndices shape).foldl
      (fun state i => if active i then state.write region (offset i) (value i) else state)
      initial).mem region (offset selected) = value selected := by
  rw [masked_scatter_eq_filter]
  apply scatter_readback_list_on _ _ _ _ _ selected
    ((TileShape.allIndices_nodup shape).filter _) (by simp [TileShape.mem_allIndices, hit])
  intro i hi j hj same
  exact injective i j (of_decide_eq_true (List.mem_filter.mp hi).2)
    (of_decide_eq_true (List.mem_filter.mp hj).2) same

#axiomsClean write_memory_congr
#axiomsClean masked_scatter_regs
#axiomsClean scatter_memory_congr
#axiomsClean masked_scatter_memory_congr
#axiomsClean scatter_readback_list_on
#axiomsClean masked_scatter_readback_on
end VeriTile.Triton.FP.Structural.State
