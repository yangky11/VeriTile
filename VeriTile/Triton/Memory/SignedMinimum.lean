import VeriTile.Triton.Memory.SignedClamp

/-! Signed minimum and nonnegative subtraction for bounded natural indices.
The word comparison is signed, matching native address/control arithmetic. -/
namespace VeriTile.Triton.AddressBounds

def signedMinimum {width : Nat} (first second : BitVec width) : BitVec width :=
  if first.slt second then first else second

theorem signedMinimum_ofNat (magnitude first second : Nat)
    (firstFits : first < 2^magnitude) (secondFits : second < 2^magnitude) :
    signedMinimum (BitVec.ofNat (magnitude+1) first) (BitVec.ofNat (magnitude+1) second) =
      BitVec.ofNat (magnitude+1) (min first second) := by
  simp only [signedMinimum,BitVec.slt,signed_ofNat magnitude first firstFits,
    signed_ofNat magnitude second secondFits,Int.ofNat_lt,decide_eq_true_eq,min_def_lt]
  split <;> rfl

theorem signedMinimum_signed (magnitude first second : Nat)
    (firstFits : first < 2^magnitude) (secondFits : second < 2^magnitude) :
    (signedMinimum (BitVec.ofNat (magnitude+1) first) (BitVec.ofNat (magnitude+1) second)).toInt =
      ((min first second : Nat) : Int) := by
  rw [signedMinimum_ofNat magnitude first second firstFits secondFits]
  exact signed_ofNat magnitude _ (Nat.lt_of_le_of_lt (min_le_left _ _) firstFits)

theorem sub_nonnegative_ofNat (magnitude value amount : Nat)
    (valueFits : value < 2^magnitude) (amountFits : amount < 2^magnitude) (nonnegative : amount ≤ value) :
    BitVec.ofNat (magnitude+1) value-BitVec.ofNat (magnitude+1) amount =
      BitVec.ofNat (magnitude+1) (value-amount) := by
  apply BitVec.eq_of_toInt_eq
  rw [sub_ofNat_signed magnitude value amount valueFits amountFits,
    signed_ofNat magnitude (value-amount) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) valueFits)]
  omega

#axiomsClean signedMinimum_ofNat
#axiomsClean signedMinimum_signed
#axiomsClean sub_nonnegative_ofNat
end VeriTile.Triton.AddressBounds
