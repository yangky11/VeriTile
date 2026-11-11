import VeriTile.Triton.Memory.AddressBounds

/-! Fixed-width signed subtraction followed by a zero clamp. This connects a
common index expression to natural subtraction without requiring its intermediate
difference to be nonnegative. The input bounds still rule out signed overflow. -/
namespace VeriTile.Triton.AddressBounds

/-- Execute a word subtraction, compare its signed result, then select zero. -/
def clippedSubWord {width : Nat} (value amount : BitVec width) : BitVec width :=
  let difference := value-amount
  if difference.slt 0 then 0 else difference

theorem sub_ofNat_signed (magnitude value amount : Nat)
    (valueFits : value < 2^magnitude) (amountFits : amount < 2^magnitude) :
    (BitVec.ofNat (magnitude+1) value-BitVec.ofNat (magnitude+1) amount).toInt =
      (value : Int)-(amount : Int) := by
  rw [BitVec.toInt_sub,signed_ofNat magnitude value valueFits,signed_ofNat magnitude amount amountFits]
  apply Int.bmod_eq_of_le_mul_two <;>
    simp only [Nat.pow_succ,Int.natCast_mul] <;> omega

theorem clippedSubWord_signed (magnitude value amount : Nat)
    (valueFits : value < 2^magnitude) (amountFits : amount < 2^magnitude) :
    (clippedSubWord (BitVec.ofNat (magnitude+1) value) (BitVec.ofNat (magnitude+1) amount)).toInt =
      ((value-amount : Nat) : Int) := by
  have signed := sub_ofNat_signed magnitude value amount valueFits amountFits
  have zero : (0 : BitVec (magnitude+1)).toInt = 0 := by simp
  simp only [clippedSubWord,BitVec.slt,signed,zero,decide_eq_true_eq]
  split
  · rw [zero]
    omega
  · rw [signed]
    omega

theorem clippedSubWord_ofNat (magnitude value amount : Nat)
    (valueFits : value < 2^magnitude) (amountFits : amount < 2^magnitude) :
    clippedSubWord (BitVec.ofNat (magnitude+1) value) (BitVec.ofNat (magnitude+1) amount) =
      BitVec.ofNat (magnitude+1) (value-amount) := by
  apply BitVec.eq_of_toInt_eq
  rw [clippedSubWord_signed magnitude value amount valueFits amountFits,
    signed_ofNat magnitude (value-amount) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) valueFits)]

#axiomsClean sub_ofNat_signed
#axiomsClean clippedSubWord_signed
#axiomsClean clippedSubWord_ofNat
end VeriTile.Triton.AddressBounds
