import VeriTile.Triton.Float.MinimumExpression
import VeriTile.Triton.DSL.RetainedSource

/-! A typed source minimum retains load promotion and final storage conversion.
Its numerical meaning comes only from the separately supplied minimum call. -/
namespace VeriTile.Tests.MinimumExpression
open VeriTile.Triton FP.Structural FP.Equational
noncomputable section
set_option backward.isDefEq.respectTransparency false

def signature : CallSignature where
  floatingPointers := [("input",.fp32),("out",.fp32)]

def source (input out : RegionName) : RetainedSource :=
  retain_triton_signature signature in triton {
    value = tl.load(input + tl.program_id(0))
    result = tl.minimum(value, 1.0)
    tl.store(out + tl.program_id(0), result)
  }

theorem source_minimum {α : Type} [Inhabited α] (base : Algebra (Term α))
    (input out : RegionName) (state : State (Term α)) :
    (exec (withMinimumCalls base) (source input out).kernel state).map
      (fun final => final.mem out (state.pids 0)) =
    some (.mk .fp32 (base.cast none .real .fp32 (.app (.minimum none .real)
      [base.cast (some .fp32) .fp32 .real ((state.mem input (state.pids 0)).read .fp32),
       base.literal none .real 1.0]))) := by
  have scalarIndices : TileShape.allIndices [] = [()] := rfl
  simp [source,exec,run,step,evalExpr,evalOp_unfold,store,
    withMinimumCalls,scalarIndices,Region.cast,State.setReg,State.write,ofFloat,toFloat,bop]

#axiomsClean source_minimum
end
end VeriTile.Tests.MinimumExpression
