import VeriTile.Triton.Float.AtomicInterleavingCorrect
import VeriTile.Triton.Float.AtomicInterleavingTraceProjection
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

private theorem source_dependencies : bodyDependencies (fun _ => False) source.kernel.surfaceBody := by
  simp only [source,ComputeKernel.surfaceBody,bodyDependencies,readDependencies,accessReads,maskReads,Region.cast]
  repeat first | trivial | constructor

private theorem jobs_dependencies : ∀ i : Fin jobs.length,
    bodyDependencies (fun _ => False) jobs[i].kernel.surfaceBody := by
  intro ⟨i,inside⟩
  match i with
  | 0 => exact source_dependencies
  | 1 => exact source_dependencies
  | n+2 => simp [jobs] at inside

/-- Replay only the emitted primitive writes, starting from the actual seed. -/
def tracedObservation (schedule : List (Fin jobs.length)) : Option Nat :=
  (runWriteEvents jobs schedule (initial jobs starting)).map fun events =>
    ((events.map Prod.snd).foldl (fun old event => event.atCell "observed" 0 old)
      (starting.mem "observed" 0)).read .fp32

private theorem traced_result (schedule : List (Fin jobs.length)) (value : Nat)
    (result : observed schedule = some (value,0,0)) : tracedObservation schedule = some value := by
  obtain ⟨final,executed,readback⟩ := Option.map_eq_some_iff.mp result
  obtain ⟨events,generated,memory⟩ := run_write_events jobs (fun _ => False) schedule
    (initial jobs starting) final (initial_dependencies jobs _ starting jobs_dependencies) executed starting
  have observedValue : (final.memory "observed" 0).read .fp32 = value := congrArg Prod.fst readback
  unfold tracedObservation
  rw [generated]
  simp only [Option.map_some,Option.some.injEq]
  rw [← MemoryWrite.applyAll_read]
  change ((MemoryWrite.applyAll (events.map Prod.snd) { starting with mem := (initial jobs starting).memory }).mem "observed" 0).read .fp32 = value
  rw [← memory]
  exact observedValue

theorem sequential_trace : tracedObservation sequential = some 12 := traced_result sequential 12 sequential_result

theorem alternating_trace : tracedObservation alternating = some 21 := traced_result alternating 21 alternating_result

theorem trace_order_is_observable : tracedObservation sequential ≠ tracedObservation alternating := by
  rw [sequential_trace,alternating_trace]
  decide

private theorem jobs_readOnly : ∀ i : Fin jobs.length,
    readOnlyBody (fun _ => False) jobs[i].kernel.surfaceBody := by
  have allowed : readOnlyBody (fun _ => False) source.kernel.surfaceBody := by
    simp [source,ComputeKernel.surfaceBody,readOnlyBody,readOnly,accessOutside]
  intro ⟨i,inside⟩
  match i with
  | 0 => exact allowed
  | 1 => exact allowed
  | n+2 => simp [jobs] at inside

/-- Shared atomic old words may differ from isolated execution, while every
worker's actual sequence of primitive input operands is still preserved. -/
theorem atomic_operand_streams (before after : State Nat) (executed : Run jobs before after) :
    ∃ events, runWriteEvents jobs executed.schedule (initial jobs before) = some events ∧
      ∀ i : Fin jobs.length, ∃ isolated, jobs[i].run before = some isolated ∧
        ((initial jobs before).locals i).WriteAdvances jobs[i].backend (workerEvents events i) ⟨[],isolated⟩ :=
  Run.project_trace jobs (fun _ => False) before after executed jobs_readOnly jobs_dependencies

#axiomsClean atomic_operand_streams
#axiomsClean sequential_trace
#axiomsClean alternating_trace
#axiomsClean trace_order_is_observable
#axiomsClean source_tick
#axiomsClean sequential_result
#axiomsClean alternating_result
#axiomsClean order_is_observable
end
end FPAtomicInterleavingTests
