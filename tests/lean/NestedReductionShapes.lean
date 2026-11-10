import VeriTile.Triton.DSL.RetainedSource
import VeriTile.Triton.Float.Structural
import VeriTile.Meta.StatementAudit

/-! Nested reductions retain their actual axes at symbolic tile dimensions.
The rank proof must not depend on unfolding a particular Fin numeral. -/
namespace VeriTile.Tests.NestedReductionShapes
open VeriTile.Triton FP.Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false

def signature : CallSignature where
  floatingPointers := [("out",.fp32)]
  constexpr := ["M","N"]

def nested (out : RegionName) (M N : Nat) : RetainedSource :=
  retain_triton_signature signature in triton {
    value = tl.full([M, N], 1.0, dtype=tl.float32)
    tl.store(out, tl.max(tl.max(value, axis=1), axis=0))
  }

def staged (out : RegionName) (M N : Nat) : RetainedSource :=
  retain_triton_signature signature in triton {
    value = tl.full([M, N], 1.0, dtype=tl.float32)
    rows = tl.max(value, axis=1)
    tl.store(out, tl.max(rows, axis=0))
  }

theorem nested_executes {α : Type} [Inhabited α] (arithmetic : Algebra α) (state : State α)
    (out : RegionName) (M N : Nat) (positiveM : 0 < M) (positiveN : 0 < N) :
    (exec arithmetic (nested out M N).kernel state).map (fun final => final.mem out 0) =
      some (.mk .fp32 (arithmetic.cast none .real .fp32
          (arithmetic.reduceMax (some .fp32) (shape := [M]) ⟨0,by simp⟩ Bool.false
            (arithmetic.reduceMax (some .fp32) (shape := [M,N]) ⟨1,by simp⟩ Bool.false
              (fun _ => arithmetic.literal (some .fp32) .real 1.0)) ()))) := by
  have scalarIndices : TileShape.allIndices [] = [()] := rfl
  simp [nested,exec,run,step,evalExpr,evalOp_unfold,store,State.setReg,
    State.write,scalarIndices,Region.cast,ofFloat,toFloat,evalComputeOp_full,evalComputeOp_alg,
    TileShape.axisDim,TileShape.eraseAxis,positiveM,positiveN]

theorem staged_executes {α : Type} [Inhabited α] (arithmetic : Algebra α) (state : State α)
    (out : RegionName) (M N : Nat) (positiveM : 0 < M) (positiveN : 0 < N) :
    (exec arithmetic (staged out M N).kernel state).map (fun final => final.mem out 0) =
      some (.mk .fp32 (arithmetic.cast none .real .fp32
          (arithmetic.reduceMax (some .fp32) (shape := [M]) ⟨0,by simp⟩ Bool.false
            (arithmetic.reduceMax (some .fp32) (shape := [M,N]) ⟨1,by simp⟩ Bool.false
              (fun _ => arithmetic.literal (some .fp32) .real 1.0)) ()))) := by
  have scalarIndices : TileShape.allIndices [] = [()] := rfl
  simp [staged,exec,run,step,evalExpr,evalOp_unfold,store,State.setReg,
    State.write,scalarIndices,Region.cast,ofFloat,toFloat,evalComputeOp_full,evalComputeOp_alg,
    TileShape.axisDim,TileShape.eraseAxis,positiveM,positiveN]


#axiomsClean TileShape.length_eraseAxis
#axiomsClean nested_executes
#axiomsClean staged_executes
end
end VeriTile.Tests.NestedReductionShapes
