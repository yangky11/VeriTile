import VeriTile.Triton.DSL.CallSignature
import VeriTile.Triton.Float.Erasure
import VeriTile.Triton.Semantics

/-! Proof automation for the real interpretation of a pasted source kernel.

The tactic unfolds the existing source projection, dtype erasure and executor;
it introduces no alternative semantics. Caller arguments supply source-specific
definitions or hypotheses. Memory folds and reduction indexing remain available
for the reusable scatter, masking and reduction lemmas after execution unfolds.
-/

open Lean TSyntax.Compat

namespace VeriTile.Triton

/-- Push a scalar memory observation through a masked scatter. This eliminates
irrelevant register state before simplifying the stored expression. -/
theorem foldl_store_readMem {α : Type} (region : RegionName)
    (offset : α → Nat) (value : α → ℝ) (active : α → Prop) [DecidablePred active]
    (readRegion : RegionName) (readOffset : Nat) (indices : List α) (s : BlockState) :
    (indices.foldl (fun state i =>
      if active i then state.writeMem region (offset i) (value i) else state) s).readMem
        readRegion readOffset =
      indices.foldl (fun previous i =>
        if active i ∧ readRegion = region ∧ readOffset = offset i then value i else previous)
        (s.readMem readRegion readOffset) := by
  induction indices generalizing s with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.foldl_cons]
      rw [ih]
      congr 1
      by_cases enabled : active head <;>
        simp [enabled, BlockState.writeMem_readMem]

/-- Normalize a pasted source kernel through the ordinary algorithm executor.
The caller may need `backward.isDefEq.respectTransparency false` locally for
dependent tile shapes on Lean 4.35. Avoid unfolding `BlockState.setReg`: its
readback lemmas eliminate irrelevant register updates without expanding memory.
-/
macro "triton_source" "[" args:Lean.Parser.Tactic.simpArg,* "]" : tactic =>
  `(tactic| simp [$args,*,
    exec, stepStmts, stepStmt, evalOp.eq_def,
    ComputeKernel.eraseDType, ComputeKernel.withScalarArguments,
    ComputeKernel.toAlgKernel, ComputeKernel.toAlgorithm?,
    ComputeStmt.listToAlgorithm?, ComputeStmt.toAlgorithm?,
    ComputeExpr.toAlgorithm?, ComputeOp.toAlgorithm?, Kernel.eraseDType,
    Stmt.eraseDTypeList, Stmt.eraseDType, Op.eraseDType, MemAccess.eraseDType,
    MaskOpt.eraseDType, FloatDType.eraseFloat, NumericDType.eraseDType,
    IntegralDType.eraseDType, ComparableDType.eraseDType,
    VeriTile.Triton.eraseDType, Region.cast,
    Tile.bop, Tile.cop, Tile.scalar, Tile.vec, NumericDType.add, NumericDType.mul,
    ComparableDType.lt, ScalarArgument.statement, ScalarArgument.dtype,
    ScalarArgument.name, ScalarArgument.value, ScalarArgument.integer,
    ComputeKernel.surfaceBody, ComputeKernel.inputs, ComputeKernel.outputs,
    ComputeKernel.fromKernelBody, ComputeDType.eraseDType,
    Except.bind, bind, pure, -Tile.scalar_eta])

end VeriTile.Triton
