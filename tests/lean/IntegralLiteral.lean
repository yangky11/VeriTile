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

def naturalBits : ComputeKernel := triton {
  offsets = tl.arange(0, 8)
  flipped = offsets ^ 1
  masked = 3 & offsets
  joined = offsets | 2
  shifted = offsets << 1
  restored = offsets >> 1
}

example : naturalBits.surfaceBody[1]? = some
    (.assign .nat [8] "flipped" (.alg (.bitXor .scalarR (.ref .nat [8] "offsets") (.constNat 1)))) := rfl
example : naturalBits.surfaceBody[2]? = some
    (.assign .nat [8] "masked" (.alg (.bitAnd .scalarL (.constNat 3) (.ref .nat [8] "offsets")))) := rfl
example : naturalBits.surfaceBody[3]? = some
    (.assign .nat [8] "joined" (.alg (.bitOr .scalarR (.ref .nat [8] "offsets") (.constNat 2)))) := rfl
example : naturalBits.surfaceBody[4]? = some
    (.assign .nat [8] "shifted" (.alg (.shiftLeft .scalarR (.ref .nat [8] "offsets") (.constNat 1)))) := rfl
example : naturalBits.surfaceBody[5]? = some
    (.assign .nat [8] "restored" (.alg (.shiftRight .scalarR (.ref .nat [8] "offsets") (.constNat 1)))) := rfl

/-- error: `^`: dtype mismatch -/
#guard_msgs in
def floatingXor : ComputeKernel := triton {
  offsets = tl.arange(0, 8)
  flipped = offsets ^ 1.0
}

/-- error: `^`: compute-only expressions such as runtime tl.bitcast must be assigned or stored directly before algorithm-layer composition -/
#guard_msgs in
def convertedXor : ComputeKernel := triton {
  offsets = tl.arange(0, 8)
  flipped = offsets ^ (1).to(tl.float32)
}

/-- A constexpr flag inside a runtime conjunction retains Boolean typing;
loop counters remain runtime natural registers. -/
def compoundFlag (enabled : Bool) : ComputeKernel := triton {
  for kind in tl.static_range(2) {
    if (enabled) and kind == 1 {
      result = kind
    }
  }
}

theorem compound_flag_structure (enabled : Bool) :
    (compoundFlag enabled).surfaceBody =
      [.forLoop "kind" 2 [.ifThen
        (.boolAnd .nil (.constBool enabled)
          (.eq .nat .nil (.ref .nat [] "kind") (.constNat 1)))
        [.assign .nat [] "result" (.alg (.ref .nat [] "kind"))]]] := rfl

#axiomsClean compound_flag_structure
end VeriTile.Tests.IntegralLiteral
