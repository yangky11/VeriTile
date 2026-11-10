import VeriTile.Triton.DSL.CallSignature
import VeriTile.Meta.StatementAudit

namespace VeriTile.Tests.RawTupleAssignment
open VeriTile.Triton

def signature : CallSignature where
  pointers := [("A",.fp32),("B",.fp32),("C",.fp32),("O",.fp32)]

def tupleSource (A B C O : RegionName) : ComputeKernel :=
  with_triton_signature signature in triton {
    x, y, z = (
      tl.load(A, True, other=0,),
      tl.load(B, True, other=0,),
      tl.load(C, True, other=0,),
    )
    for i in range(0, 2,):
      u, v = (x + 1.0, y + 2.0)
      tl.store(O + i, u + v + z,)
  }

def sequentialSource (A B C O : RegionName) : ComputeKernel :=
  with_triton_signature signature in triton {
    x = tl.load(A, True, other=0)
    y = tl.load(B, True, other=0)
    z = tl.load(C, True, other=0)
    for i in range(0, 2):
      u = x + 1.0
      v = y + 2.0
      tl.store(O + i, u + v + z)
  }

/-- Full kernel equality retains loads, nested bodies, arithmetic and stores. -/
theorem whole_program (A B C O : RegionName) :
    tupleSource A B C O = sequentialSource A B C O := rfl

/-- error: dependent tuple assignment is unsupported -/
#guard_msgs in
example : ComputeKernel :=
  with_triton_signature ({} : CallSignature) in triton {
    x = 1
    y = 2
    x, y = (y, x)
  }

/-- error: dependent tuple assignment is unsupported -/
#guard_msgs in
example : ComputeKernel :=
  with_triton_signature ({} : CallSignature) in triton {
    x = 1
    x, y = (0, x.to(tl.int32))
  }

/-- error: tuple assignment target/value counts differ -/
#guard_msgs in
example : ComputeKernel :=
  with_triton_signature ({} : CallSignature) in triton {
    x, y = (1, 2, 3)
  }

/-- error: tuple assignment requires distinct targets -/
#guard_msgs in
example : ComputeKernel :=
  with_triton_signature ({} : CallSignature) in triton {
    x, x = (1, 2)
  }

/-- error: runtime assignment shadows an integer constexpr -/
#guard_msgs in
example (N : Nat) : ComputeKernel :=
  with_triton_signature ({constexpr := ["N"]} : CallSignature) in triton {
    a, N = (1, 2)
  }

#guard DSL.RawSourceText.callTrailingCommas "f((a,),)" == "f((a,))"
#guard DSL.RawSourceText.callTrailingCommas "f(g(a,), b,)" == "f(g(a), b)"
#guard DSL.RawSourceText.callTrailingCommas "f(\"),\",)" == "f(\"),\")"
#guard DSL.RawSourceText.callTrailingCommas "x in (a,)" == "x in (a,)"
#guard DSL.RawSourceText.callTrailingCommas "if (x,):" == "if (x,):"
#guard DSL.RawSourceText.callTrailingCommas "f (x, )" == "f (x )"
#guard DSL.RawSourceText.callTrailingCommas "(x,)" == "(x,)"

#axiomsClean whole_program
end VeriTile.Tests.RawTupleAssignment
