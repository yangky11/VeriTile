import VeriTile.Triton.DSL.RetainedSource
import VeriTile.Meta.StatementAudit
import VeriTile.Triton.Float.Reshape

/-! A retained source split only reads a pre-existing local tile. Reject target
aliasing, so expansion cannot change a later RHS or duplicate a memory read. -/
namespace VeriTile.Tests.RetainedSplit
open VeriTile.Triton FP.Structural
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

def signature : CallSignature where
  constexpr := ["M","N"]

def retained (M N : Nat) : RetainedSource :=
  retain_triton_signature signature in triton {
    value = tl.full([M, 2 * N], 1.0, dtype=tl.float32)
    paired = tl.reshape(value, (M, 2, N))
    interleaved = tl.permute(paired, (0, 2, 1))
    left, right = tl.split(interleaved)
  }

def explicit (M N : Nat) : ComputeKernel :=
  with_triton_signature signature in triton {
    value = tl.full([M, 2 * N], 1.0, dtype=tl.float32)
    paired = tl.reshape(value, [M, 2, N])
    interleaved = tl.permute(paired, [0, 2, 1])
    left = tl.split(interleaved, 0)
    right = tl.split(interleaved, 1)
  }

theorem complete_source (M N : Nat) : (retained M N).kernel = explicit M N := rfl

/-- The retained source's layout suffix preserves arbitrary accumulator values,
including padded lanes. Only the initializer is replaced by a symbolic register
for this proof; the authoritative kernel remains the readable retained source. -/
theorem layout_suffix {α : Type} [Inhabited α] (A : Algebra α) (s : State α)
    (M N : Nat) (value : Values α .real [M,2*N]) :
    ∃ final, run A ((retained M N).kernel.surfaceBody.drop 1)
      (s.setReg "value" .real [M,2*N] value) = some final ∧
      final.regs .real [M,N] "left" = some (fun i => value
        (i.1,⟨i.2.1.val,by omega⟩,PUnit.unit)) ∧
      final.regs .real [M,N] "right" = some (fun i => value
        (i.1,⟨N+i.2.1.val,by omega⟩,PUnit.unit)) ∧
      final.mem = s.mem := by
  refine ⟨?final,?execution,?left,?right,?memory⟩
  case execution =>
    simp [retained,ComputeKernel.surfaceBody,run,step,evalExpr,evalOp_unfold,TileShape.product]
    rfl
  case left =>
    simp only [State.setReg_ne_name _ _ _ _ _ _ _ _ (by decide : ("left" : String) ≠ "right"),State.setReg_same]
    congr 1
    funext i
    change value (TileShape.reshapeIndex (input := [M,2*N]) (output := [M,2,N]) _ (i.1,(0 : Fin 2),i.2.1,PUnit.unit)) = _
    rw [TileShape.reshapeIndex_groupColumns]
    simp only [Fin.val_zero,Nat.zero_mul,Nat.zero_add]
  case right =>
    simp only [State.setReg_same]
    congr 1
    funext i
    change value (TileShape.reshapeIndex (input := [M,2*N]) (output := [M,2,N]) _ (i.1,(1 : Fin 2),i.2.1,PUnit.unit)) = _
    rw [TileShape.reshapeIndex_groupColumns]
    simp only [Fin.val_one,Nat.one_mul]
  case memory => rfl

/-- error: split assignment requires distinct targets -/
#guard_msgs in
example : ComputeKernel :=
  with_triton_signature ({} : CallSignature) in triton {
    source = tl.full([2], 1.0, dtype=tl.float32)
    same, same = tl.split(source)
  }

/-- error: split assignment cannot overwrite its source register -/
#guard_msgs in
example : ComputeKernel :=
  with_triton_signature ({} : CallSignature) in triton {
    source = tl.full([2], 1.0, dtype=tl.float32)
    source, right = tl.split(source)
  }

/-- error: tl.split: final dimension must be the literal 2 -/
#guard_msgs in
example : ComputeKernel :=
  with_triton_signature ({} : CallSignature) in triton {
    source = tl.full([4, 3], 1.0, dtype=tl.float32)
    left, right = tl.split(source)
  }

#axiomsClean complete_source
#axiomsClean layout_suffix
end

def retainedText : String := triton_source_text (retained 4 8)
#guard (retainedText.splitOn "left, right = tl.split(interleaved)").length == 2
end VeriTile.Tests.RetainedSplit
