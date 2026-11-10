import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import VeriTile.Meta.StatementAudit

/-! Ownership geometry for square tiles computed in one triangle and mirrored
off the diagonal. These lemmas concern addresses only: mirroring ownership does
not assert equal floating values, commutative dot products, or identical compiler
contraction at the two stores. Source runs must separately prove their writes. -/
namespace VeriTile.Triton.TriangularTiles

def count (size width : Nat) : Nat := (size + width - 1) / width

def owner (width row column : Nat) : Nat × Nat :=
  (max (row / width) (column / width),min (row / width) (column / width))

/-- An active lower-triangular program owns its direct block and, only off the
diagonal, its transposed block. Bounds are supplied by the caller's store mask. -/
def Owns (width blockRow blockColumn row column : Nat) : Prop :=
  blockColumn ≤ blockRow ∧
    ((row / width = blockRow ∧ column / width = blockColumn) ∨
      (blockColumn < blockRow ∧ row / width = blockColumn ∧ column / width = blockRow))

theorem owns_iff_owner (width blockRow blockColumn row column : Nat) :
    Owns width blockRow blockColumn row column ↔ owner width row column = (blockRow,blockColumn) := by
  simp only [Owns,owner,Prod.mk.injEq]
  omega

theorem unique {width row column a b c d : Nat}
    (first : Owns width a b row column) (second : Owns width c d row column) : a=c ∧ b=d := by
  have one := (owns_iff_owner ..).mp first
  have two := (owns_iff_owner ..).mp second
  exact Prod.mk.inj (one.symm.trans two)

theorem covered (width row column : Nat) :
    Owns width (owner width row column).1 (owner width row column).2 row column := by
  apply (owns_iff_owner ..).mpr
  rfl

theorem tile_in_range {size width coordinate : Nat} (positive : 0 < width)
    (inside : coordinate < size) : coordinate / width < count size width := by
  apply (Nat.div_lt_iff_lt_mul positive).mpr
  have remainder := Nat.mod_lt (size+width-1) positive
  have division := Nat.mod_add_div (size+width-1) width
  unfold count
  rw [Nat.mul_comm width] at division
  omega

theorem owner_in_grid {size width row column : Nat} (positive : 0 < width)
    (hr : row < size) (hc : column < size) :
    (owner width row column).1 < count size width ∧
      (owner width row column).2 < count size width := by
  have r := tile_in_range positive hr
  have c := tile_in_range positive hc
  simp only [owner]
  omega

/-- Actual lane formulas used by both stores recover their program IDs. -/
theorem lane_block {width lane : Nat} (positive : 0 < width) (inside : lane < width)
    (block : Nat) : (block * width + lane) / width = block := by
  rw [Nat.mul_comm block width,Nat.mul_add_div positive,Nat.div_eq_of_lt inside,Nat.add_zero]

theorem direct_owned {width blockRow blockColumn i j : Nat}
    (positive : 0 < width) (active : blockColumn ≤ blockRow) (hi : i < width) (hj : j < width) :
    Owns width blockRow blockColumn (blockRow*width+i) (blockColumn*width+j) := by
  exact ⟨active,Or.inl ⟨lane_block positive hi _,lane_block positive hj _⟩⟩

theorem mirror_owned {width blockRow blockColumn i j : Nat}
    (positive : 0 < width) (active : blockColumn < blockRow) (hi : i < width) (hj : j < width) :
    Owns width blockRow blockColumn (blockColumn*width+j) (blockRow*width+i) := by
  exact ⟨Nat.le_of_lt active,Or.inr ⟨active,lane_block positive hj _,lane_block positive hi _⟩⟩

theorem direct_mirror_disjoint {width blockRow blockColumn row column : Nat}
    (offDiagonal : blockColumn < blockRow)
    (direct : row / width = blockRow ∧ column / width = blockColumn) :
    ¬ (row / width = blockColumn ∧ column / width = blockRow) := by omega

/-- Bounded row-major addresses do not alias, before adding any native pointer
base. The outer index may itself be a batch/row encoding. -/
theorem rowMajor_injective {width i j k l : Nat} (positive : 0 < width)
    (hj : j < width) (hl : l < width) (same : i*width+j = k*width+l) : i=k ∧ j=l := by
  have first := congrArg (fun value => value / width) same
  have second := congrArg (fun value => value % width) same
  rw [lane_block positive hj,lane_block positive hl] at first
  simpa [Nat.add_mod,Nat.mod_eq_of_lt hj,Nat.mod_eq_of_lt hl] using And.intro first second

#axiomsClean owns_iff_owner
#axiomsClean unique
#axiomsClean covered
#axiomsClean tile_in_range
#axiomsClean owner_in_grid
#axiomsClean lane_block
#axiomsClean direct_owned
#axiomsClean mirror_owned
#axiomsClean direct_mirror_disjoint
#axiomsClean rowMajor_injective
end VeriTile.Triton.TriangularTiles
