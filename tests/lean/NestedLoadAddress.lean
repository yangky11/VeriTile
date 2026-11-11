import VeriTile.Triton.DSL.RetainedSource

namespace VeriTile.Tests.NestedLoadAddress
open VeriTile.Triton

-- The constant offset is used only inside a casted read. It must remain an
-- address integer even though the loaded numerical value becomes FP32.
def source (X : RegionName) : ComputeKernel := triton {
  tl.region X = tl.bfloat16
  base = 0
  offsets = base + tl.arange(0, 4)
  value = tl.load(X + offsets).to(tl.float32)
}

example (X : RegionName) : (source X).surfaceBody[0]? =
    some (.assign .nat [] "base" (.alg (.constNat 0))) := rfl

-- Both constexpr paths retain their own offset shape and integer carrier.
def branched (X : RegionName) (flag : Bool) : ComputeKernel := triton {
  tl.region X = tl.bfloat16
  if flag {
    base = tl.arange(0, 2)[:, None]
  } else {
    base = 0
  }
  offsets = base + tl.arange(0, 4)[None, :]
  value = tl.load(X + offsets).to(tl.float32)
}

private def resultKind : ComputeStmt → Option (TileDType × TileShape)
  | .assign dtype shape _ _ => some (dtype,shape)
  | _ => none

-- Address inference must not turn the loaded numerical result into Nat.
example (X : RegionName) : ((source X).surfaceBody[2]?).bind resultKind =
    some (.real,[4]) := rfl

/-- error: nat expression: dtype mismatch -/
#guard_msgs in
def floatingOffset (X : RegionName) : ComputeKernel := triton {
  tl.region X = tl.bfloat16
  base = 0.0
  offsets = base + tl.arange(0, 4)
  value = tl.load(X + offsets).to(tl.float32)
}

end VeriTile.Tests.NestedLoadAddress
