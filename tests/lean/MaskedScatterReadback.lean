import VeriTile.Triton.Float.Scatter

namespace VeriTile.Tests.MaskedScatterReadback
open Triton FP.Structural
noncomputable section

-- A 2-by-2 tile writes a width-one matrix. Inactive (0,1) aliases active
-- (1,0), so global address injectivity is false and must not be required.
def offset (i : TileIndex [2,2]) : Nat := i.1.val+i.2.1.val
def active (i : TileIndex [2,2]) : Prop := i.2.1.val=0
instance : DecidablePred active := fun _ => inferInstanceAs (Decidable (_=0))

theorem aliases : offset (0,1,PUnit.unit)=offset (1,0,PUnit.unit) := rfl

theorem active_injective (i j : TileIndex [2,2]) (hi : active i) (hj : active j)
    (same : offset i=offset j) : i=j := by
  change i.2.1.val=0 at hi
  change j.2.1.val=0 at hj
  have row : i.1.val=j.1.val := by simpa [offset,hi,hj] using same
  have column : i.2.1.val=j.2.1.val := hi.trans hj.symm
  exact Prod.ext (Fin.ext row) (Prod.ext (Fin.ext column) (Subsingleton.elim _ _))

theorem padded_readback (initial : State Nat) (values : TileIndex [2,2] → Cell Nat)
    (selected : TileIndex [2,2]) (hit : active selected) :
    ((TileShape.allIndices [2,2]).foldl
      (fun state i => if active i then state.write "output" (offset i) (values i) else state)
      initial).mem "output" (offset selected)=values selected :=
  State.masked_scatter_readback_on _ _ _ _ _ _ hit active_injective

#axiomsClean aliases
#axiomsClean active_injective
#axiomsClean padded_readback
end
end VeriTile.Tests.MaskedScatterReadback
