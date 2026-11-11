import VeriTile.Triton.Float.Structural
import VeriTile.Meta.StatementAudit

/-! Explicit cases for the dependent compute evaluator. These avoid requiring
Lean to synthesize equations for unrelated unsupported bitcast combinations. -/
namespace VeriTile.Triton.FP.Structural

theorem evalComputeOp_bitcast_signed {α : Type} [Inhabited α] (M : Algebra α)
    (e : ComputeOp .int32 shape) (s : State α) :
    evalComputeOp M (.bitcast .int32 .fp32 rfl e) s =
      ((evalComputeOp M e s).bind fun value =>
        some (fun i => M.fp32Bits ⟨BitVec.ofInt 32 (value i)⟩)) := rfl

theorem evalComputeOp_bitcast_unsigned {α : Type} [Inhabited α] (M : Algebra α)
    (e : ComputeOp .uint32 shape) (s : State α) :
    evalComputeOp M (.bitcast .uint32 .fp32 rfl e) s =
      ((evalComputeOp M e s).bind fun value =>
        some (fun i => M.fp32Bits ⟨BitVec.ofNat 32 (value i)⟩)) := rfl

theorem evalComputeOp_load_fp32 {α : Type} [Inhabited α] (M : Algebra α)
    (memory : MemAccess .real shape) (mask : MaskOpt .real shape) (padding : PaddingOption)
    (s : State α) :
    evalComputeOp M (.load .fp32 memory mask padding) s =
      ((evalOp M (some .fp32) (.load .real memory mask padding) s).bind fun value =>
        some (fun i => M.fp32Load (value i))) := rfl

#axiomsClean evalComputeOp_bitcast_signed
#axiomsClean evalComputeOp_bitcast_unsigned
#axiomsClean evalComputeOp_load_fp32
end VeriTile.Triton.FP.Structural
