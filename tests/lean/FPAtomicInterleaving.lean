import VeriTile.Triton.Float.AtomicInterleavingCorrect
import VeriTile.Triton.DSL.RetainedSource
import VeriTile.Meta.StatementAudit

/-! Order-sensitive countermodel: these are source/control tests, not a claim
that hardware maximum is decimal concatenation. A commutation law cannot be
smuggled in through the interpreter or by sharing program-local registers. -/
namespace FPAtomicInterleavingTests
open VeriTile.Triton FP.Structural Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

private def arithmetic : Algebra Nat where
  literal := fun _ _ _ => 0
  negInf := 0
  binary := fun _ _ operation x y => if operation = .add then x+y else 999
  unary := fun _ _ value => value
  cast := fun _ _ _ value => value
  fromNat := fun _ value => value
  fromInt := fun _ value => value.toNat
  fp32Bits := fun word => word.bits.toNat
  fp32Load := id
  atomicReduce := fun operation dtype =>
    if operation = .max ∧ dtype = .fp32 then some (fun old value => old*10+value) else none
  reduceMax := fun _ {shape} _ _ values _ =>
    match (TileShape.allIndices shape).head? with
    | some i => values i
    | none => 0
  reduceSum := fun _ {shape} _ _ values _ =>
    match (TileShape.allIndices shape).head? with
    | some i => values i
    | none => 0

private theorem arithmetic_cast : arithmetic.cast = fun _ _ _ value => value := rfl
private theorem arithmetic_reduce : arithmetic.atomicReduce .max .fp32 = some (fun old value => old*10+value) := rfl

private theorem arithmetic_literal : arithmetic.literal = fun _ _ _ => 0 := rfl
private theorem arithmetic_add : arithmetic.binary (some .fp32) .real .add = Nat.add := rfl

private def signature : CallSignature where
  floatingPointers := [("observed",.fp32)]
  scalars := [("payload",.fp32)]

def source : RetainedSource :=
  let observed : RegionName := "observed"
  retain_triton_signature signature in triton {
    tl.atomic_max(observed, payload + 0.0)
  }

def job (pid : Nat) : Invocation Nat where
  kernel := source.kernel
  backend := arithmetic
  arguments := [⟨"payload",.real,[],fun _ => pid+1⟩]
  clearRegisters := Bool.true
  pids := fun _ => pid

def jobs := [job 0,job 1]
private instance : NeZero jobs.length := ⟨by decide⟩

private def starting : State Nat where
  mem := fun region offset => if region = "input" then .mk .fp32 (offset+1) else .mk .fp32 0
  regs := fun _ _ _ => none
  pids := fun _ => 0
  numPids := fun _ => 2
  undef := fun dtype _ _ => defaultValue dtype

def sequential : List (Fin jobs.length) := [0,1]

def alternating : List (Fin jobs.length) := [1,0]

def observed (schedule : List (Fin jobs.length)) : Option (Nat × Nat × Nat) :=
  (Interleaved.run jobs schedule (initial jobs starting)).map fun final =>
    ((final.memory "observed" 0).read .fp32,(final.locals 0).pending.length,(final.locals 1).pending.length)

private def sourceBody : List Command :=
  match source.kernel with | .mk _ _ body => commands body

private theorem source_tick (s : State Nat) (memory : Memory Nat) (value : Nat)
    (payload : s.regs .real [] "payload" = some (fun _ => value)) :
    (Local.mk sourceBody s).tick arithmetic memory =
      some ⟨[], ({s with mem := memory}).write "observed" 0
        (.mk .fp32 (((memory "observed" 0).read .fp32)*10+value))⟩ := by
  have scalarIndices : TileShape.allIndices [] = [()] := rfl
  simp [sourceBody, source, commands, Local.tick, leafSupported,
    step,evalExpr,evalOp_unfold,atomicReduction,atomicAdd,atomicAddition,
    arithmetic_cast,arithmetic_reduce,arithmetic_literal,arithmetic_add,
    payload,scalarIndices,Region.cast,ofFloat,toFloat,numeric,bop]

private theorem backend_lookup (i : Fin jobs.length) : jobs[i].backend = arithmetic := by
  rcases i with ⟨i,h⟩
  match i with
  | 0 => rfl
  | 1 => rfl
  | n+2 => simp [jobs] at h
private theorem jobs_length : jobs.length = 2 := rfl
private theorem initial_local (i : Fin jobs.length) :
    (initial jobs starting).locals i = ⟨sourceBody,(job i.val).initial starting⟩ := by
  rcases i with ⟨i,h⟩
  match i with
  | 0 => rfl
  | 1 => rfl
  | n+2 => simp [jobs] at h
private theorem payload_read (pid : Nat) :
    ((job pid).initial starting).regs .real [] "payload" = some (fun _ => pid+1) := by
  simp [job,Invocation.initial,bindRegisters,State.setReg]

private theorem initial_memory : (initial jobs starting).memory = starting.mem := rfl
private theorem backend (pid : Nat) : (job pid).backend = arithmetic := rfl

theorem sequential_result : observed sequential = some (12,0,0) := by
  simp only [observed,sequential,Interleaved.run,tick,initial_local,
    backend_lookup,initial_memory,source_tick _ _ _ (payload_read _)]
  simp [Function.update,jobs_length,initial_local,source_tick _ _ _ (payload_read _),State.write,Cell.read]
  simp [starting]

theorem alternating_result : observed alternating = some (21,0,0) := by
  simp only [observed,alternating,Interleaved.run,tick,initial_local,
    backend_lookup,initial_memory,source_tick _ _ _ (payload_read _)]
  simp [Function.update,jobs_length,initial_local,source_tick _ _ _ (payload_read _),State.write,Cell.read]
  simp [starting]

theorem order_is_observable : observed sequential ≠ observed alternating := by
  rw [sequential_result,alternating_result]
  decide

#axiomsClean source_tick
#axiomsClean sequential_result
#axiomsClean alternating_result
#axiomsClean order_is_observable
end
end FPAtomicInterleavingTests
