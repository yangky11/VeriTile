import VeriTile.Triton.Core.ReshapeIndex

/-! Reversing the minor axis of a grouped reshape preserves the row and group.
This is an exact coordinate identity for arbitrary tile payloads and group
widths; it does not rely on a floating-point law or enumerate concrete lanes. -/
namespace VeriTile.Triton.TileShape

/-- The flat column represented by a group and its minor-axis lane. -/
def groupedColumn {groups width : Nat} (group : Fin groups) (lane : Fin width) :
    Fin (groups*width) :=
  ⟨group.val*width+lane.val,by
    calc
      _ < group.val*width+width := Nat.add_lt_add_left lane.isLt _
      _ = (group.val+1)*width := (Nat.succ_mul _ _).symm
      _ ≤ groups*width := Nat.mul_le_mul_right width group.isLt⟩

theorem reshapeIndex_ungroupColumns {rows groups width : Nat}
    (row : Fin rows) (group : Fin groups) (lane : Fin width) :
    reshapeIndex (input := [rows,groups,width]) (output := [rows,groups*width])
      (by simp [product]) (row,groupedColumn group lane,PUnit.unit) =
      (row,group,lane,PUnit.unit) := by
  have grouped := reshapeIndex_groupColumns row group lane
  unfold groupedColumn
  rw [← grouped]
  exact reshapeIndex_roundtrip _ _

/-- The exact index map of `reshape(flip(reshape(x), dim=2))`. The two reshapes
retain every lane, including masked padding; only the minor-axis lane reverses. -/
theorem reshapeIndex_groupedFlip {rows groups width : Nat}
    (row : Fin rows) (group : Fin groups) (lane : Fin width) :
    reshapeIndex (input := [rows,groups*width]) (output := [rows,groups,width])
      (by simp [product])
      (flipIndex [rows,groups,width] ⟨2,by simp⟩
        (reshapeIndex (input := [rows,groups,width]) (output := [rows,groups*width])
          (by simp [product]) (row,groupedColumn group lane,PUnit.unit))) =
      (row,groupedColumn group lane.rev,PUnit.unit) := by
  rw [reshapeIndex_ungroupColumns]
  exact reshapeIndex_groupColumns row group lane.rev

#axiomsClean reshapeIndex_ungroupColumns
#axiomsClean reshapeIndex_groupedFlip
end VeriTile.Triton.TileShape
