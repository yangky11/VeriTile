import VeriTile.Triton.Core.Shape
import VeriTile.Meta.StatementAudit

/-! A final-axis coordinate is transported without dropping data, including
scalar leadinges and empty axes. These inverses support external tensor layouts. -/
namespace VeriTile.Triton.TileShape

theorem splitLast_appendAxis (shape : TileShape) (index : TileIndex shape) (last : Fin n) :
    splitLastIndex shape (appendAxisIndex shape index last) = (index,last) := by
  induction shape with
  | nil => cases index; rfl
  | cons d rest ih => simp only [appendAxisIndex,splitLastIndex,ih]

theorem appendAxis_splitLast (shape : TileShape) (index : TileIndex (shape ++ [n])) :
    appendAxisIndex shape (splitLastIndex shape index).1 (splitLastIndex shape index).2 = index := by
  induction shape with
  | nil => rcases index with ⟨last,tailUnit⟩; cases tailUnit; rfl
  | cons d rest ih =>
    simp only [appendAxisIndex,splitLastIndex]
    exact congrArg (Prod.mk index.1) (ih index.2)

def appendAxisEquiv (shape : TileShape) (n : Nat) :
    (TileIndex shape × Fin n) ≃ TileIndex (shape ++ [n]) where
  toFun := fun index => appendAxisIndex shape index.1 index.2
  invFun := splitLastIndex shape
  left_inv := fun index => splitLast_appendAxis shape index.1 index.2
  right_inv := appendAxis_splitLast shape

/-- The final axis, for arbitrary leading rank. -/
def lastAxis (leading : TileShape) (width : Nat) : Fin (leading ++ [width]).length :=
  ⟨leading.length,by simp⟩

@[simp] theorem eraseAxis_last (leading : TileShape) (width : Nat) :
    eraseAxis (leading ++ [width]) (lastAxis leading width) = leading := by
  induction leading with
  | nil => rfl
  | cons d rest ih =>
      change d :: eraseAxis (rest ++ [width]) (lastAxis rest width) = d :: rest
      rw [ih]

@[simp] theorem axisDim_last (leading : TileShape) (width : Nat) :
    axisDim (leading ++ [width]) (lastAxis leading width) = width := by
  induction leading with
  | nil => rfl
  | cons d rest ih => exact ih

#axiomsClean eraseAxis_last
#axiomsClean axisDim_last
#axiomsClean splitLast_appendAxis
#axiomsClean appendAxis_splitLast
#axiomsClean appendAxisEquiv
end VeriTile.Triton.TileShape
