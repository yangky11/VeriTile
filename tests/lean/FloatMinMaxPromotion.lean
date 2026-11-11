import VeriTile.Triton.DSL
import VeriTile.Meta.StatementAudit

namespace VeriTile.Tests.FloatMinMaxPromotion
open VeriTile.Triton

def mixedMax (x : RegionName) (B : Nat) : ComputeKernel := triton {
  tl.region x = tl.bfloat16
  m = tl.full([$(B)], value=-float("inf"), dtype=tl.float32)
  inp = tl.load(x + tl.arange(0, $(B)))
  m_new = tl.maximum(m, inp)
}

def mixedMin (x : RegionName) (B : Nat) : ComputeKernel := triton {
  tl.region x = tl.float16
  m = tl.full([$(B)], value=0.0, dtype=tl.float32)
  inp = tl.load(x + tl.arange(0, $(B)))
  m_new = tl.minimum(inp, m)
}

def literalMax (x : RegionName) (B : Nat) : ComputeKernel := triton {
  tl.region x = tl.float16
  inp = tl.load(x + tl.arange(0, $(B)))
  m_new = tl.maximum(0.0, inp)
}

/-- The input remains bf16 storage and is widened at the floating maximum. -/
example (x : RegionName) (B : Nat) :
    (mixedMax x B).surfaceBody.getLast? = some
      (.assign .real [B] "m_new" (.compute (.alg .fp32
        (.maximumFloat .real (.consSame .nil) (.ref .real [B] "m")
          (.castFloat .bf16 .real (.ref .bf16 [B] "inp")))))) := rfl

/-- Reversing operand order still promotes the half tensor to fp32. -/
example (x : RegionName) (B : Nat) :
    (mixedMin x B).surfaceBody.getLast? = some
      (.assign .real [B] "m_new" (.compute (.alg .fp32
        (.minimumFloat .real (.consSame .nil)
          (.castFloat .fp16 .real (.ref .fp16 [B] "inp")) (.ref .real [B] "m"))))) := rfl

private def assignedHalf : ComputeStmt → Bool
  | .assign .fp16 _ _ _ => Bool.true
  | _ => Bool.false

/-- A constexpr literal does not promote a half tensor to fp32. -/
example (x : RegionName) (B : Nat) :
    (literalMax x B).surfaceBody.getLast?.map assignedHalf = some Bool.true := rfl

def bfloatLiteralSquare (x : RegionName) (B : Nat) : ComputeKernel := triton {
  tl.region x = tl.bfloat16
  inp = tl.load(x + tl.arange(0, $(B)))
  positive = tl.maximum(inp, 0)
  squared = positive * positive
}

def bfloatPairMinimum (x y : RegionName) (B : Nat) : ComputeKernel := triton {
  tl.region x = tl.bfloat16
  tl.region y = tl.bfloat16
  a = tl.load(x + tl.arange(0, $(B)))
  b = tl.load(y + tl.arange(0, $(B)))
  result = tl.minimum(a, b)
}

/-- BF16 maximum is promoted before squaring: there is no BF16 product round. -/
example (x : RegionName) (B : Nat) :
    (bfloatLiteralSquare x B).surfaceBody.drop 1 =
      [.assign .real [B] "positive" (.compute (.alg .fp32
        (.maximumFloat .real .scalarR (.castFloat .bf16 .real (.ref .bf16 [B] "inp"))
          (.const 0)))),
       .assign .real [B] "squared" (.compute (.alg .fp32
        (.mul .real (.consSame .nil) (.ref .real [B] "positive") (.ref .real [B] "positive"))))] := rfl

example (x y : RegionName) (B : Nat) :
    (bfloatPairMinimum x y B).surfaceBody.getLast? = some
      (.assign .real [B] "result" (.compute (.alg .fp32
        (.minimumFloat .real (.consSame .nil)
          (.castFloat .bf16 .real (.ref .bf16 [B] "a"))
          (.castFloat .bf16 .real (.ref .bf16 [B] "b")))))) := rfl

#guard_msgs (drop info) in
#auditModuleAxioms

end VeriTile.Tests.FloatMinMaxPromotion
