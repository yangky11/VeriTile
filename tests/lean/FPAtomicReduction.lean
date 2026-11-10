import VeriTile.Triton.Float.AtomicExpression
import VeriTile.Triton.Float.ExecutionProfile
import VeriTile.Triton.Float.StructuralSafety
import VeriTile.Triton.DSL.RetainedSource
import VeriTile.Meta.StatementAudit

/-! Typed atomic max/min retain their own numerical primitive. These are
single-program execution checks; concurrent grid scheduling is separate. -/
namespace FPAtomicReductionTests
open VeriTile.Triton FP.Structural
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

theorem max_reads_previous_update (M : Algebra α) (s : State α) (a b : α)
    (f : α → α → α) (available : M.atomicReduce .max .fp32 = some f) :
    atomicReduction M .max (.region ⟨"observed"⟩ (.full [2] (.constNat 0))) .none
      (fun i : TileIndex [2] => if i.1.val = 0 then a else b : Values α .fp32 [2]) s =
    some (s.write "observed" 0 (.mk .fp32 (f (f ((s.mem "observed" 0).read .fp32) a) b))) := by
  have indices : TileShape.allIndices [2] = [(0,PUnit.unit),(1,PUnit.unit)] := by decide
  simp [atomicReduction,atomicAdd,atomicAddition,available,evalOp_unfold,indices,
    Region.cast,State.write,Cell.read]
  funext region offset
  by_cases hit : region = "observed" ∧ offset = 0 <;> simp [hit]

theorem min_mask_preserves_other_cells (M : Algebra α) (s : State α)
    (v : Values α .bf16 [2]) (f : α → α → α)
    (available : M.atomicReduce .min .bf16 = some f) :
    (atomicReduction M .min (.region ⟨"observed"⟩ (.arange 2))
      (.mask (.lt .nat .scalarR (.arange 2) (.constNat 1))) v s).map
      (fun t => (t.mem "observed" 0,t.mem "observed" 1,t.mem "frame" 0,t.regs)) =
    some (.mk .bf16 (f ((s.mem "observed" 0).read .bf16) (v (0,PUnit.unit))),
      s.mem "observed" 1,s.mem "frame" 0,s.regs) := by
  have indices : TileShape.allIndices [2] = [(0,PUnit.unit),(1,PUnit.unit)] := by decide
  simp [atomicReduction,atomicAdd,atomicAddition,available,evalOp_unfold,indices,
    numericLt,natLt,bop,Region.cast,State.write]

theorem missing_backend_fails_even_empty (M : Algebra α) (s : State α)
    (missing : M.atomicReduce .max .fp32 = none) :
    atomicReduction M .max (.region ⟨"observed"⟩ (.arange 0)) .none
      (fun i : TileIndex [0] => Fin.elim0 i.1 : Values α .fp32 [0]) s = none := by
  simp [atomicReduction,atomicAdd,atomicAddition,missing]

theorem return_value_remains_rejected (M : Algebra α) (s : State α) :
    step M (.atomicRMW .max .fp32 [] (.region ⟨"observed"⟩ (.constNat 0))
      (.alg (.ref .fp32 [] "v")) none .none (some "old")) s = none := by simp [step]

theorem non_reduction_remains_rejected (M : Algebra α) (s : State α)
    (v : Values α .fp32 []) :
    atomicReduction M .xchg (.region ⟨"observed"⟩ (.constNat 0)) .none v s = none := by
  simp [atomicReduction]

omit [Inhabited α] in
theorem profile_retains_backend (M : Algebra α) (precision : ComputeDType) :
    (M.withDefaultPrecision precision).atomicReduce = M.atomicReduce := rfl

def signature : CallSignature where
  floatingPointers := [("input",.fp32),("observed",.fp32)]

def source : RetainedSource :=
  let input : RegionName := "input"
  let observed : RegionName := "observed"
  retain_triton_signature signature in triton {
    i = tl.arange(0, 2)
    value = tl.load(input + i)
    tl.atomic_max(observed + i * 0, value, mask=i < 1)
  }


/-- The retained source reaches the typed atomic backend and retains its mask;
ordinary maximum and atomic addition do not determine this result. -/
theorem source_executes (M : Algebra α) (s : State α) (f : α → α → α)
    (available : M.atomicReduce .max .fp32 = some f) :
    (exec M source.kernel s).map (fun final =>
      (final.mem "observed" 0,final.mem "observed" 1,final.mem "frame" 0)) =
    some (.mk .fp32 (f ((s.mem "observed" 0).read .fp32)
      (M.cast none .fp32 .fp32 ((s.mem "input" 0).read .fp32))),
      s.mem "observed" 1,s.mem "frame" 0) := by
  have indices : TileShape.allIndices [2] = [(0,PUnit.unit),(1,PUnit.unit)] := by decide
  simp [source,exec,run,step,evalExpr,evalOp_unfold,atomicReduction,atomicAdd,atomicAddition,
    available,indices,State.setReg,State.write,Region.cast,numeric,numericLt,natLt,bop,
    toFloat,ofFloat]


/-- Inline operands must use the same declared storage as assigned loads. -/
def nestedSource : RetainedSource :=
  let input : RegionName := "input"
  let observed : RegionName := "observed"
  retain_triton_signature signature in triton {
    tl.atomic_max(observed, tl.load(input + tl.program_id(0)))
  }

theorem nested_source_executes (M : Algebra α) (s : State α) (f : α → α → α)
    (available : M.atomicReduce .max .fp32 = some f) :
    exec M nestedSource.kernel s = some (s.write "observed" 0
      (.mk .fp32 (f ((s.mem "observed" 0).read .fp32)
        (M.cast none .fp32 .fp32 ((s.mem "input" (s.pids 0)).read .fp32))))) := by
  have indices : TileShape.allIndices [] = [()] := rfl
  simp [nestedSource,exec,run,step,evalExpr,evalOp_unfold,atomicReduction,atomicAdd,
    atomicAddition,available,indices,Region.cast,ofFloat,toFloat]

#axiomsClean nested_source_executes

def scalarSignature : CallSignature where
  floatingPointers := [("observed",.fp32)]
  scalars := [("payload",.fp32)]

def scalarSource : RetainedSource :=
  let observed : RegionName := "observed"
  retain_triton_signature scalarSignature in triton {
    tl.atomic_max(observed, payload)
  }

theorem scalar_source_executes (M : Algebra α) (s : State α) (value : α)
    (f : α → α → α) (available : M.atomicReduce .max .fp32 = some f)
    (bound : s.regs .real [] "payload" = some (fun _ => value)) :
    exec M scalarSource.kernel s = some (s.write "observed" 0
      (.mk .fp32 (f ((s.mem "observed" 0).read .fp32) (M.cast none .real .fp32 value)))) := by
  have indices : TileShape.allIndices [] = [()] := rfl
  simp [scalarSource,exec,run,step,evalExpr,evalOp_unfold,atomicReduction,atomicAdd,
    atomicAddition,available,bound,indices,Region.cast,ofFloat,toFloat]

/-- Repeated-address source updates retain their expression order. -/
theorem symbolic_order (M : Algebra (FP.Equational.Term α))
    (s : State (FP.Equational.Term α)) (a b : FP.Equational.Term α) :
    atomicReduction (FP.Equational.atomicExpressionBackend M) .max
      (.region ⟨"observed"⟩ (.full [2] (.constNat 0))) .none
      (fun i : TileIndex [2] => if i.1.val = 0 then a else b : Values (FP.Equational.Term α) .fp32 [2]) s =
    some (s.write "observed" 0 (.mk .fp32
      (.app (.atomicReduce .max .fp32)
        [.app (.atomicReduce .max .fp32) [(s.mem "observed" 0).read .fp32,a],b]))) := by
  exact max_reads_previous_update (FP.Equational.atomicExpressionBackend M) s a b
    (fun previous incoming => .app (.atomicReduce .max .fp32) [previous,incoming])
    (by simp [FP.Equational.atomicExpressionBackend])

def untyped_max (out : RegionName) : ComputeKernel := triton {
  value := 1
  tl.atomic_max($(out), value)
}

theorem unknown_storage_still_fails (out : RegionName) :
    (untyped_max out).toAlgorithm? = Except.error (.requiresEffectProjection "tl.atomic_max") := rfl

/-- error: tl.atomic_max: unsupported option -/
#guard_msgs in
example : RetainedSource :=
  let input : RegionName := "input"
  let observed : RegionName := "observed"
  retain_triton_signature signature in triton {
    value = tl.load(input)
    tl.atomic_max(observed, value, dtype=tl.float32)
  }

#guard_msgs (drop info) in
#auditModuleAxioms
end FPAtomicReductionTests
