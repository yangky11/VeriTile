import VeriTile.Triton.DSL.CallSignature
import VeriTile.Meta.StatementAudit

/-! Source admission regressions. The retained body is unchanged Inductor output;
this module tests elaboration and literal interpretation, not RMSNorm correctness. -/
namespace VeriTile.Tests.RawSourceIntegration
open VeriTile.Triton
noncomputable section

def signature : CallSignature where
  pointers := [("in_ptr0",.fp32),("in_ptr1",.fp32),("out_ptr1",.fp32)]
  scalars := [("xnumel",.integer),("r0_numel",.integer)]
  constexpr := ["XBLOCK"]
  helperAliases := [("libdevice.rsqrt",.rsqrt)]
  literalPolicy := .pythonFloat32

def sourceKernel (in_ptr0 in_ptr1 out_ptr1 : RegionName) (XBLOCK : Nat) : ComputeKernel :=
  with_triton_signature signature in triton {
    xnumel = 2
    r0_numel = 8
    R0_BLOCK: tl.constexpr = 8
    rnumel = r0_numel
    RBLOCK: tl.constexpr = R0_BLOCK
    xoffset = tl.program_id(0) * XBLOCK
    xindex = xoffset + tl.arange(0, XBLOCK)[:, None]
    xmask = xindex < xnumel
    r0_index = tl.arange(0, R0_BLOCK)[None, :]
    r0_offset = 0
    r0_mask = tl.full([XBLOCK, R0_BLOCK], True, tl.int1)
    roffset = r0_offset
    rindex = r0_index
    r0_1 = r0_index
    x0 = xindex
    tmp0 = tl.load(in_ptr0 + (r0_1 + 8*x0), xmask, other=0.0)
    tmp12 = tl.load(in_ptr1 + (r0_1), None, eviction_policy='evict_last')
    tmp1 = tmp0 * tmp0
    tmp2 = tl.broadcast_to(tmp1, [XBLOCK, R0_BLOCK])
    tmp4 = tl.where(xmask, tmp2, 0)
    tmp5 = tl.sum(tmp4, 1)[:, None].to(tl.float32)
    tmp6 = 8.0
    tmp7 = (tmp5 / tmp6)
    tmp8 = 9.999999747378752e-06
    tmp9 = tmp7 + tmp8
    tmp10 = libdevice.rsqrt(tmp9)
    tmp11 = tmp0 * tmp10
    tmp13 = tmp11 * tmp12
    tl.store(out_ptr1 + (r0_1 + 8*x0), tmp13, xmask)
  }


def literal : ComputeKernel :=
  with_triton_signature ({literalPolicy := .pythonFloat32} : CallSignature) in triton {
    epsilon = 9.999999747378752e-06
  }
def explicitLiteral : ComputeKernel := triton {
  epsilon = $(((2748779 : ℝ) / 274877906944 : ℝ))
}
example : literal = explicitLiteral := by rfl

def ordinaryDecimal : ComputeKernel :=
  with_triton_signature ({literalPolicy := .pythonFloat32} : CallSignature) in triton {
    epsilon = 1e-5
  }
example : ordinaryDecimal = explicitLiteral := by rfl

/-- Exactly representable integer syntax remains available to index lowering. -/
def exactInteger (X : RegionName) : ComputeKernel :=
  with_triton_signature ({pointers := [("X",.fp32)], literalPolicy := .pythonFloat32} : CallSignature) in triton {
    index = tl.program_id(0) * 16777216
    value = tl.load(X + index)
  }

/-- error: integer literal is not exactly representable in float32; context-dependent scalar promotion is unsupported -/
#guard_msgs in
example (X : RegionName) : ComputeKernel :=
  with_triton_signature ({pointers := [("X",.fp32)], literalPolicy := .pythonFloat32} : CallSignature) in triton {
    value = tl.load(X + 0)
    result = value + 16777217
  }

-- These execute the frontend conversion, including subnormals and overflow.
#guard DSL.SourceLiterals.scientificFloat32 1 Bool.true 5 == some (2748779 / 274877906944)
#guard DSL.SourceLiterals.scientificFloat32 1 Bool.true 45 == some ((1 : Rat) / 2^149)
#guard DSL.SourceLiterals.scientificFloat32 1 Bool.true 50 == some 0
#guard DSL.SourceLiterals.scientificFloat32 1 Bool.false 40 == none
#guard DSL.SourceLiterals.binary32Rational 0x80000000 == some 0
#guard DSL.SourceLiterals.binary32Rational 0xbf800000 == some (-1)
#guard DSL.SourceLiterals.scientificFloat32 16777217 Bool.false 0 == some 16777216
-- Halfway cases round to an even significand, after Python binary64 parsing.
#guard DSL.SourceLiterals.scientificFloat32 1000000059604644775390625 Bool.true 24 == some 1
#guard DSL.SourceLiterals.scientificFloat32 1000000178813934326171875 Bool.true 24 == some ((4194305 : Rat) / 4194304)

/-- A None positional mask is absence of masking, including cache kwargs. -/
def noneMask (X Y : RegionName) : ComputeKernel :=
  with_triton_signature ({pointers := [("X",.fp32),("Y",.fp32)]} : CallSignature) in triton {
    x = tl.load(X + 0, None, eviction_policy='evict_last')
    tl.store(Y + 0, x, None)
  }
def omittedMask (X Y : RegionName) : ComputeKernel :=
  with_triton_signature ({pointers := [("X",.fp32),("Y",.fp32)]} : CallSignature) in triton {
    x = tl.load(X + 0, eviction_policy='evict_last')
    tl.store(Y + 0, x)
  }
example (X Y : RegionName) : noneMask X Y = omittedMask X Y := by rfl

/-- None in a slice must not erase a real mask. -/
def expandedMask (X : RegionName) : ComputeKernel :=
  with_triton_signature ({pointers := [("X",.fp32)]} : CallSignature) in triton {
    offsets = tl.arange(0, 4)
    mask = offsets < 3
    values = tl.load(X + offsets[None, :], mask[None, :], other=0.0)
  }

/-- error: Python floating literal is nonfinite after float32 conversion -/
#guard_msgs in
example : ComputeKernel :=
  with_triton_signature ({literalPolicy := .pythonFloat32} : CallSignature) in triton {
    x = 1e40
  }

/-- error: pythonFloat32 literals require FP32 floating storage -/
#guard_msgs in
example (X : RegionName) : ComputeKernel :=
  with_triton_signature ({pointers := [("X",.fp64)], literalPolicy := .pythonFloat32} : CallSignature) in triton {
    x = tl.load(X + 0)
  }

/-- error: unsupported multi-result source helper -/
#guard_msgs in
example : ComputeKernel :=
  with_triton_signature ({} : CallSignature) in triton {
    x, y = unknown(1)
  }

/-- error: assignment shadows a source helper binding -/
#guard_msgs in
example : ComputeKernel :=
  with_triton_signature ({helperAliases := [("libdevice.rsqrt",.rsqrt)]} : CallSignature) in triton {
    libdevice = 0
  }

/-- error: pythonFloat32 literals do not support non-FP32 floating conversions -/
#guard_msgs in
example : ComputeKernel :=
  with_triton_signature ({literalPolicy := .pythonFloat32} : CallSignature) in triton {
    x = tl.full([4], 1.0, tl.float64)
  }

#guard_msgs (drop info) in
#auditModuleAxioms
end
end VeriTile.Tests.RawSourceIntegration
