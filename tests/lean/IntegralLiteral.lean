import VeriTile.Triton.DSL.RetainedSource
import VeriTile.Meta.StatementAudit

namespace VeriTile.Tests.IntegralLiteral
open VeriTile.Triton

def natural (heads : Nat) : ComputeKernel := triton {
  h = tl.program_id(0)
  group = h // (heads // 2)
  lane = h % 2
}

def signed (X : RegionName) : ComputeKernel := triton {
  tl.region X = tl.int64
  h = tl.load(X)
  group = h // -2
  lane = h % 3
}

example (heads : Nat) : (natural heads).surfaceBody[2]? = some
    (.assign .nat [] "lane" (.alg (Op.tritonMod .nat .nil (.ref .nat [] "h") (.constNat 2)))) := rfl

example (X : RegionName) : (signed X).surfaceBody[2]? = some
    (.assign .int [] "lane" (.alg (Op.tritonMod .int .nil (.ref .int [] "h") (.constInt 3)))) := rfl

example (X : RegionName) : (signed X).surfaceBody[1]? = some
    (.assign .int [] "group" (.alg (Op.tritonDiv .int .nil (.ref .int [] "h") (.constInt (-2))))) := rfl

def literalLeft (X : RegionName) : ComputeKernel := triton {
  tl.region X = tl.int64
  h = tl.load(X)
  group = -17 // h
  lane = -17 % h
}

example (X : RegionName) : (literalLeft X).surfaceBody[2]? = some
    (.assign .int [] "lane" (.alg (Op.tritonMod .int .nil (.constInt (-17)) (.ref .int [] "h")))) := rfl

-- A floating literal does not silently become an integer divisor.
/-- error: runtime integer division: dtype mismatch -/
#guard_msgs in
def floatingDivisor : ComputeKernel := triton {
  h = tl.program_id(0)
  group = h // 2.0
}

/-- error: runtime integer remainder: dtype mismatch -/
#guard_msgs in
def floatingRemainder : ComputeKernel := triton {
  h = tl.program_id(0)
  lane = h % 2.0
}

end VeriTile.Tests.IntegralLiteral
