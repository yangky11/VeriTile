import VeriTile.Triton.DSL
import VeriTile.Triton.Float.Structural
import VeriTile.Meta.StatementAudit

/-! Inductor's helpers are ordered selections, not native extrema primitives.
Pinned helper implementation:
https://github.com/pytorch/pytorch/blob/v2.9.1/torch/_inductor/runtime/triton_helpers.py#L94-L107
These tests retain the source call and check its structural expression against
an explicit comparison/NaN/select program. No GPU conformity is assumed. -/
namespace VeriTile.Tests.InductorExtrema
open VeriTile.Triton
noncomputable section

def maximum (A B O : RegionName) : ComputeKernel := triton {
  tl.region A = tl.float32, B = tl.float32, O = tl.float32
  a = tl.load(A + 0)
  b = tl.load(B + 0)
  value = triton_helpers.maximum(a, b)
  tl.store(O + 0, value)
}

def explicitMaximum (A B O : RegionName) : ComputeKernel := triton {
  tl.region A = tl.float32, B = tl.float32, O = tl.float32
  a = tl.load(A + 0)
  b = tl.load(B + 0)
  value = tl.where(tl.logical_or(a > b, a != a), a, b)
  tl.store(O + 0, value)
}

theorem maximum_selection (A B O : RegionName) :
    (maximum A B O).surfaceBody = (explicitMaximum A B O).surfaceBody := rfl

def minimum (A B O : RegionName) : ComputeKernel := triton {
  tl.region A = tl.bfloat16, B = tl.bfloat16, O = tl.bfloat16
  a = tl.load(A + 0)
  b = tl.load(B + 0)
  value = triton_helpers.minimum(a, b)
  tl.store(O + 0, value)
}

def explicitMinimum (A B O : RegionName) : ComputeKernel := triton {
  tl.region A = tl.bfloat16, B = tl.bfloat16, O = tl.bfloat16
  a = tl.load(A + 0)
  b = tl.load(B + 0)
  value = tl.where(tl.logical_or(a < b, a != a), a, b)
  tl.store(O + 0, value)
}

theorem minimum_selection_bf16 (A B O : RegionName) :
    (minimum A B O).surfaceBody = (explicitMinimum A B O).surfaceBody := rfl

def selectedExpression : ComputeExpr .real [] := .compute (.alg .fp32
  (.where (.boolOr .nil
      (.gt .real .nil (.ref .real [] "a") (.ref .real [] "b"))
      (.ne .real .nil (.ref .real [] "a") (.ref .real [] "a")))
    (.ref .real [] "a") (.ref .real [] "b")))

theorem maximum_expression (A B O : RegionName) :
    (maximum A B O).surfaceBody[2]? = some (.assign .real [] "value" selectedExpression) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Opaque comparison policies are the only premises; the original words are
selected without an arithmetic round or a maximum primitive. -/
theorem selection_execution {α : Type} [Inhabited α]
    (M : FP.Structural.Algebra α) (s : FP.Structural.State α)
    (a b : α) (lt eq : α → α → Bool)
    (hlt : M.compareLt (some .fp32) .real = some lt)
    (heq : M.compareEq (some .fp32) .real = some eq)
    (ha : s.regs .real [] "a" = some (fun _ => a))
    (hb : s.regs .real [] "b" = some (fun _ => b)) :
    FP.Structural.evalExpr M selectedExpression s =
      some (fun _ => if lt b a || !(eq a a) then a else b) := by
  simp [selectedExpression, FP.Structural.evalExpr, FP.Structural.evalComputeOp_alg,
    FP.Structural.evalOp_unfold, FP.Structural.numericLt, FP.Structural.numericEq,
    hlt, heq, ha, hb, FP.Structural.bop, ComputeDType.eraseDType]

private def assignedBfloat : ComputeStmt → Bool
  | .assign .bf16 _ _ _ => Bool.true
  | _ => Bool.false

theorem helper_retains_bf16 (A B O : RegionName) :
    (minimum A B O).surfaceBody[2]?.map assignedBfloat = some Bool.true := rfl

def literalMaximum (A O : RegionName) (N : Nat) : ComputeKernel := triton {
  tl.region A = tl.float32, O = tl.float32
  a = tl.load(A + tl.arange(0, $(N)))
  value = triton_helpers.maximum(a, 1e-08)
  tl.store(O + tl.arange(0, $(N)), value)
}

def signedMaximum (A O : RegionName) (N : Nat) : ComputeKernel := triton {
  tl.region A = tl.int32, O = tl.int32
  a = tl.load(A + tl.arange(0, $(N)))
  value = triton_helpers.maximum(a, -1)
  tl.store(O + tl.arange(0, $(N)), value)
}

/-- error: comparison: dtype mismatch -/
#guard_msgs in
example (A : RegionName) : ComputeKernel := triton {
  tl.region A = tl.bfloat16
  a = tl.load(A + 0)
  value = triton_helpers.maximum(a, 0.0)
}

#axiomsClean maximum_expression
#axiomsClean selection_execution
#axiomsClean helper_retains_bf16
#axiomsClean maximum_selection
#axiomsClean minimum_selection_bf16
end
end VeriTile.Tests.InductorExtrema
