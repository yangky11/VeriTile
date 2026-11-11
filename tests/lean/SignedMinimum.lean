import VeriTile.Triton.Memory.SignedMinimum

namespace VeriTile.Tests.SignedMinimum
open VeriTile.Triton.AddressBounds

example : signedMinimum (5#32) (3#32) = 3#32 := by decide
example : signedMinimum (3#32) (5#32) = 3#32 := by decide
example : signedMinimum (3#32) (3#32) = 3#32 := by decide
example : signedMinimum (0xffffffff#32) (3#32) = 0xffffffff#32 := by decide
example : signedMinimum (0x7fffffff#32) (0#32) = 0#32 := by decide
example : signedMinimum (0x7fffffffffffffff#64) (3#64) = 3#64 := by decide
example : signedMinimum (0xffffffffffffffff#64) (3#64) = 0xffffffffffffffff#64 := by decide
example : (BitVec.ofNat 32 7)-(BitVec.ofNat 32 7) = BitVec.ofNat 32 0 :=
  sub_nonnegative_ofNat 31 7 7 (by decide) (by decide) (by decide)
example : (BitVec.ofNat 64 9)-(BitVec.ofNat 64 1) = BitVec.ofNat 64 8 :=
  sub_nonnegative_ofNat 63 9 1 (by decide) (by decide) (by decide)

#axiomsClean signedMinimum_ofNat
#axiomsClean signedMinimum_signed
#axiomsClean sub_nonnegative_ofNat
end VeriTile.Tests.SignedMinimum
