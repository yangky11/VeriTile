import VeriTile.Triton.Memory.Strided
import Init.Data.BitVec.Lemmas

/-! Reusable native-width admission for nonnegative affine address arithmetic.
Bounds concern every supplied coordinate, including masked-off padded lanes.
They prove integer offset arithmetic, not CUDA pointer allocation or execution. -/
namespace VeriTile.Triton.AddressBounds
open VeriTile.Triton

/-- Word execution of the same rank-polymorphic multiply/add address formula. -/
def offsetWord (width : Nat) : {shape : TileShape} → Strided.Strides shape → TileIndex shape → BitVec width
  | [], _, _ => 0
  | _ :: _, strides, index =>
    BitVec.ofNat width index.1.val * BitVec.ofNat width strides.1 + offsetWord width strides.2 index.2

/-- Modular word operations agree with the mathematical affine formula before
any range assumption. Range admission below rules out a changed signed value. -/
theorem offsetWord_eq (width : Nat) {shape : TileShape} (strides : Strided.Strides shape)
    (index : TileIndex shape) : offsetWord width strides index = BitVec.ofNat width (Strided.offset strides index) := by
  induction shape with
  | nil => rfl
  | cons n tail ih =>
    simp only [offsetWord,Strided.offset,ih,BitVec.ofNat_mul,BitVec.ofNat_add]

/-- Use `magnitude=63` for nonnegative signed 64-bit address arithmetic. -/
theorem signed_ofNat (magnitude value : Nat) (bound : value < 2^magnitude) :
    (BitVec.ofNat (magnitude+1) value).toInt = (value : Int) := by
  have wider : value < 2^(magnitude+1) := by
    rw [Nat.pow_succ]
    omega
  have natural : (BitVec.ofNat (magnitude+1) value).toNat = value := by
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt wider]
  rw [BitVec.toInt_eq_toNat_of_lt, natural]
  rw [natural,Nat.pow_succ]
  omega

/-- A closed envelope checked once for an entire padded tile or launch grid.
Zero strides and overlapping views are allowed. `scale` can convert element
addresses to byte offsets without losing the multiplication's range check. -/
def Fits (magnitude base scale : Nat) {shape : TileShape} (strides : Strided.Strides shape) : Prop :=
  base + scale * Strided.lastOffset strides < 2^magnitude

instance (magnitude base scale : Nat) {shape : TileShape} (strides : Strided.Strides shape) :
    Decidable (Fits magnitude base scale strides) := inferInstanceAs (Decidable (_ < _))

theorem affine_bound (magnitude base scale : Nat) {shape : TileShape} (strides : Strided.Strides shape)
    (admitted : Fits magnitude base scale strides) (index : TileIndex shape) :
    base + scale * Strided.offset strides index < 2^magnitude :=
  Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_left scale (Strided.offset_le_last strides index)) base) admitted

theorem affine_word_signed (magnitude base scale : Nat) {shape : TileShape} (strides : Strided.Strides shape)
    (admitted : Fits magnitude base scale strides) (index : TileIndex shape) :
    (BitVec.ofNat (magnitude+1) base + BitVec.ofNat (magnitude+1) scale *
      offsetWord (magnitude+1) strides index).toInt =
      ((base + scale * Strided.offset strides index : Nat) : Int) := by
  rw [offsetWord_eq,← BitVec.ofNat_mul,← BitVec.ofNat_add]
  exact signed_ofNat magnitude _ (affine_bound magnitude base scale strides admitted index)

/-- Every lane of a launched tile fits the padded extent, regardless of the
logical load/store mask. This is the bound needed before pointer evaluation. -/
theorem tiled_lane_bound (tiles width block lane : Nat) (hb : block < tiles) (hl : lane < width) :
    block*width+lane < tiles*width := by
  calc
    _ < block*width+width := Nat.add_lt_add_left hl _
    _ = (block+1)*width := by simp only [Nat.add_mul,Nat.one_mul]
    _ ≤ tiles*width := Nat.mul_le_mul_right width hb

#axiomsClean offsetWord_eq
#axiomsClean signed_ofNat
#axiomsClean affine_bound
#axiomsClean affine_word_signed
#axiomsClean tiled_lane_bound
end VeriTile.Triton.AddressBounds
