import VeriTile.Triton.Core.GroupedFlip

open VeriTile.Triton TileShape

-- Empty leading/group axes need no extra positive-size premise; there is simply
-- no output coordinate. Width is arbitrary, so this is not a two-lane template.
example (rows groups width : Nat) (r : Fin rows) (g : Fin groups) (j : Fin width) :
    reshapeIndex (input := [rows,groups*width]) (output := [rows,groups,width])
      (by simp [product])
      (flipIndex [rows,groups,width] ⟨2,by simp⟩
        (reshapeIndex (input := [rows,groups,width]) (output := [rows,groups*width])
          (by simp [product]) (r,groupedColumn g j,PUnit.unit))) =
      (r,groupedColumn g j.rev,PUnit.unit) :=
  reshapeIndex_groupedFlip r g j
