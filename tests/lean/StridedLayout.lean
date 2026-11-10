import VeriTile.Triton.Memory.Strided

namespace VeriTile.Tests.StridedLayout
open Triton Strided

example : span (shape := [2,3]) (7,2,PUnit.unit) = 12 := rfl
example : span (shape := [3,2]) (2,7,PUnit.unit) = 12 := rfl
example : span (shape := [2,0]) (7,2,PUnit.unit) = 0 := rfl
example : span (shape := []) PUnit.unit = 1 := rfl
example : span (shape := [2,3]) (0,0,PUnit.unit) = 1 := rfl

/-- A transposed, gapped view uses the same backing allocation. -/
theorem transposed_bound (i : TileIndex [3,2]) : offset (shape := [3,2]) (2,7,PUnit.unit) i < 12 :=
  offset_lt_span _ i

#axiomsClean transposed_bound
end VeriTile.Tests.StridedLayout
