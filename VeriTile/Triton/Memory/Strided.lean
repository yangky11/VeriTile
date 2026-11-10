import VeriTile.Triton.Core.Shape
import VeriTile.Meta.StatementAudit
import Lean.Elab.Tactic.Omega

/-! Rank-polymorphic nonnegative element strides and backing spans.
Zero strides and overlapping views are allowed for address bounds; uniqueness
of logical values in such views is a separate IO obligation. -/
namespace VeriTile.Triton.Strided

def Strides : TileShape → Type
  | [] => PUnit
  | _ :: tail => Nat × Strides tail

def offset : {shape : TileShape} → Strides shape → TileIndex shape → Nat
  | [], _, _ => 0
  | _ :: _, strides, index => index.1.val*strides.1 + offset strides.2 index.2

def lastOffset : {shape : TileShape} → Strides shape → Nat
  | [], _ => 0
  | n :: _, strides => (n-1)*strides.1 + lastOffset strides.2

/-- Empty views require no backing; a scalar occupies one element. -/
def span {shape : TileShape} (strides : Strides shape) : Nat :=
  if TileShape.product shape = 0 then 0 else lastOffset strides+1

theorem product_positive {shape : TileShape} (index : TileIndex shape) :
    0 < TileShape.product shape := by
  induction shape with
  | nil => exact Nat.zero_lt_one
  | cons n tail ih =>
    exact Nat.mul_pos (Nat.zero_lt_of_lt index.1.isLt) (ih index.2)

theorem offset_le_last {shape : TileShape} (strides : Strides shape) (index : TileIndex shape) :
    offset strides index ≤ lastOffset strides := by
  induction shape with
  | nil => exact Nat.le_refl _
  | cons n tail ih =>
    have coordinate : index.1.val ≤ n-1 := by have := index.1.isLt; omega
    exact Nat.add_le_add (Nat.mul_le_mul_right strides.1 coordinate) (ih strides.2 index.2)

theorem offset_lt_span {shape : TileShape} (strides : Strides shape) (index : TileIndex shape) :
    offset strides index < span strides := by
  have nonempty := Nat.ne_of_gt (product_positive index)
  simp only [span, nonempty, ite_false]
  exact Nat.lt_succ_of_le (offset_le_last strides index)

theorem empty_span {shape : TileShape} (strides : Strides shape)
    (empty : TileShape.product shape=0) : span strides=0 := by simp [span,empty]

#axiomsClean product_positive
#axiomsClean offset_le_last
#axiomsClean offset_lt_span
#axiomsClean empty_span
end VeriTile.Triton.Strided
