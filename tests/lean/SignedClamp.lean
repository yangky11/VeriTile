import VeriTile.Triton.Memory.SignedClamp

open VeriTile.Triton.AddressBounds

example (value amount : Nat) (valueFits : value < 2^31) (amountFits : amount < 2^31) :
    clippedSubWord (BitVec.ofNat 32 value) (BitVec.ofNat 32 amount) = BitVec.ofNat 32 (value-amount) :=
  clippedSubWord_ofNat 31 value amount valueFits amountFits

-- The raw word subtraction really becomes negative at the first token; the
-- signed clamp, rather than unsigned subtraction, recovers the logical index.
#guard ((0#32)-(1#32)).toInt = -1
#guard clippedSubWord (0#32) (1#32) = 0#32
#guard clippedSubWord (1#32) (1#32) = 0#32
#guard clippedSubWord (2#32) (1#32) = 1#32
#guard clippedSubWord (0x7fffffff#32) (0#32) = 0x7fffffff#32
#guard clippedSubWord (0#32) (0x7fffffff#32) = 0#32

-- Outside the admission range, wrapping and signed comparison can change the
-- mathematical result. This is not a theorem about arbitrary unsigned words.
#guard clippedSubWord (0x80000000#32) (0#32) = 0#32
#guard clippedSubWord (0x80000000#32) (0#32) != 0x80000000#32

-- The same lemma supports other native widths, including the smallest signed
-- range. No kernel shape or token-count template is used.
example (value amount : Nat) (valueFits : value < 2^63) (amountFits : amount < 2^63) :
    (clippedSubWord (BitVec.ofNat 64 value) (BitVec.ofNat 64 amount)).toInt = ((value-amount : Nat) : Int) :=
  clippedSubWord_signed 63 value amount valueFits amountFits
#guard clippedSubWord (0#1) (0#1) = 0#1
