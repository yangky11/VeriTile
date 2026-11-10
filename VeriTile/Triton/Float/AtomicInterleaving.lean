import VeriTile.Triton.Float.ProgramIO

/-! Interleaving of actual source statements with scalar atomic operations.

Registers and control stacks are local to each invocation; memory is shared.
A schedule chooses one enabled program at each tick. Scalar atomic updates
are indivisible. Ordinary tile stores remain statement-sized steps; native
admission must establish disjoint ordinary accesses before using this bounded
model. Vector atomics, returned atomic values, barriers and async effects fail
closed. No numerical commutation or complete-kernel callback is supplied.
-/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev Memory (α : Type) := RegionName → Nat → Cell α

/-- Loop bounds are captured on entry, exactly as in Structural execution. -/
inductive Command where
  | source (statement : ComputeStmt)
  | counted (index : RegName) (current stop : Nat) (body : List ComputeStmt)
  | natural (index : RegName) (current stop stride : Nat) (body : List ComputeStmt)
  | integer (index : RegName) (current stop : Int) (stride : Nat) (body : List ComputeStmt)

def commands (body : List ComputeStmt) : List Command := body.map Command.source

structure Local (α : Type) where
  pending : List Command
  /-- The memory field is replaced by current shared memory before each tick.
  Only registers, IDs and undefined-value interpretation persist locally. -/
  state : State α

/-- These leaves use Structural.step itself. Source control is expanded below,
so an atomic hidden inside a loop cannot run as an indivisible whole loop. -/
def leafSupported : ComputeStmt → Bool
  | .assign .. | .store .. => true
  | .atomicAdd _ [] _ _ _ => true
  | .atomicRMW .max _ [] _ _ none _ none | .atomicRMW .min _ [] _ _ none _ none => true
  | .alg (.assign ..) | .alg (.store ..) => true
  | .alg (.atomicAdd _ [] _ _ _) => true
  | .alg (.atomicRMW .max _ [] _ _ none _ none)
  | .alg (.atomicRMW .min _ [] _ _ none _ none) => true
  | _ => false

/-- One thread source step, reading current shared memory. There is no caller
supplied execution function and no reassociation of an atomic update. -/
def Local.tick {α : Type} [Inhabited α] (M : Algebra α) (thread : Local α)
    (memory : Memory α) : Option (Local α) := do
  let state := { thread.state with mem := memory }
  let head :: tail := thread.pending | none
  match head with
  | .source statement =>
      if leafSupported statement then
        return ⟨tail,← step M statement state⟩
      else match statement with
      | .forLoop index stop body =>
          some ⟨.counted index 0 stop body :: tail,state⟩
      | .forRange index start stop stride body =>
          some ⟨.natural index start stop stride body :: tail,state⟩
      | .forRangeDyn index start stop stride body => do
          let first ← evalOp M none start state
          let last ← evalOp M none stop state
          let delta ← evalOp M none stride state
          some ⟨.natural index (first ()) (last ()) (delta ()) body :: tail,state⟩
      | .forRangeInt index start stop stride body => do
          let first ← evalOp M none start state
          let last ← evalOp M none stop state
          let delta ← evalOp M none stride state
          some ⟨.integer index (first ()) (last ()) (delta ()) body :: tail,state⟩
      | .ifThen condition body => do
          let selected ← evalOp M none condition state
          some ⟨(if selected () then commands body else []) ++ tail,state⟩
      | .ifThenElse condition yes no => do
          let selected ← evalOp M none condition state
          some ⟨commands (if selected () then yes else no) ++ tail,state⟩
      | _ => none
  | .counted index current stop body =>
      if current < stop then
        some ⟨commands body ++ .counted index (current+1) stop body :: tail,
          state.setReg index .nat [] (fun _ => current)⟩
      else some ⟨tail,state⟩
  | .natural index current stop stride body =>
      if stride = 0 ∨ stop ≤ current then some ⟨tail,state⟩
      else some ⟨commands body ++ .natural index (current+stride) stop stride body :: tail,
        state.setReg index .nat [] (fun _ => current)⟩
  | .integer index current stop stride body =>
      if stride = 0 ∨ stop ≤ current then some ⟨tail,state⟩
      else some ⟨commands body ++ .integer index (current+stride) stop stride body :: tail,
        state.setReg index .int [] (fun _ => current)⟩

structure Configuration (α : Type) (count : Nat) where
  memory : Memory α
  locals : Fin count → Local α

def initial {α : Type} (jobs : List (Invocation α)) (state : State α) : Configuration α jobs.length :=
  ⟨state.mem,fun i => ⟨match jobs[i].kernel with | .mk _ _ body => commands body,
    jobs[i].initial state⟩⟩

/-- Other programs' registers and pending source stay untouched by this tick. -/
def tick {α : Type} [Inhabited α] (jobs : List (Invocation α)) (selected : Fin jobs.length)
    (before : Configuration α jobs.length) : Option (Configuration α jobs.length) := do
  let after ← (before.locals selected).tick jobs[selected].backend before.memory
  return ⟨after.state.mem,Function.update before.locals selected after⟩

def run {α : Type} [Inhabited α] (jobs : List (Invocation α)) :
    List (Fin jobs.length) → Configuration α jobs.length → Option (Configuration α jobs.length)
  | [], before => some before
  | selected :: rest, before => (tick jobs selected before).bind (run jobs rest)

def Configuration.Complete {α : Type} {count : Nat} (configuration : Configuration α count) : Prop :=
  ∀ i, (configuration.locals i).pending = []

/-- A completed native execution must name a complete successful interleaving,
not merely a permutation of independently computed output formulas. -/
structure Run {α : Type} [Inhabited α] (jobs : List (Invocation α)) (before after : State α) where
  schedule : List (Fin jobs.length)
  result : Configuration α jobs.length
  executed : run jobs schedule (initial jobs before) = some result
  complete : result.Complete
  readback : after.mem = result.memory

/-- Safety checks only the statement/entry expressions actually evaluated now.
Future loop bodies are checked in their own shared states when scheduled. -/
def Local.Safe {α : Type} [Inhabited α] (M : Algebra α) (bounds : RegionName → Nat)
    (thread : Local α) (memory : Memory α) : Prop :=
  let state := { thread.state with mem := memory }
  match thread.pending with
  | [] => False
  | .source statement :: _ =>
      match statement with
      | .forLoop .. | .forRange .. => True
      | .forRangeDyn _ first last delta _ =>
          Safety.safeOp M none bounds state first ∧ Safety.safeOp M none bounds state last ∧
          Safety.safeOp M none bounds state delta
      | .forRangeInt _ first last delta _ =>
          Safety.safeOp M none bounds state first ∧ Safety.safeOp M none bounds state last ∧
          Safety.safeOp M none bounds state delta
      | .ifThen condition _ | .ifThenElse condition _ _ => Safety.safeOp M none bounds state condition
      | _ => leafSupported statement = true ∧ Safety.stepSafe M bounds statement state
  | _ => True

def Safe {α : Type} [Inhabited α] (jobs : List (Invocation α)) (bounds : RegionName → Nat) :
    List (Fin jobs.length) → Configuration α jobs.length → Prop
  | [], _ => True
  | selected :: rest, before =>
      (before.locals selected).Safe jobs[selected].backend bounds before.memory ∧
      ∀ after, tick jobs selected before = some after → Safe jobs bounds rest after

theorem tick_preserves_other_local {α : Type} [Inhabited α] (jobs : List (Invocation α))
    (selected other : Fin jobs.length) (before after : Configuration α jobs.length)
    (different : other ≠ selected) (executed : tick jobs selected before = some after) :
    after.locals other = before.locals other := by
  change ((before.locals selected).tick jobs[selected].backend before.memory).bind
    (fun thread => some (Configuration.mk thread.state.mem (Function.update before.locals selected thread))) = some after at executed
  obtain ⟨thread,_,same⟩ := Option.bind_eq_some_iff.mp executed
  have equal := Option.some.inj same
  subst after
  simp [Function.update,different]

/-- Ordinary invariant induction retains each actual intermediate shared state. -/
theorem run_invariant {α : Type} [Inhabited α] (jobs : List (Invocation α))
    (predicate : Configuration α jobs.length → Prop)
    (preserved : ∀ selected before after, predicate before → tick jobs selected before = some after → predicate after)
    (schedule : List (Fin jobs.length)) (before after : Configuration α jobs.length)
    (start : predicate before) (executed : run jobs schedule before = some after) : predicate after := by
  induction schedule generalizing before with
  | nil =>
      simp only [run,Option.some.injEq] at executed
      subst after
      exact start
  | cons selected rest ih =>
      simp only [run] at executed
      cases reduced : tick jobs selected before with
      | none => simp [reduced] at executed
      | some middle =>
          simp only [reduced,Option.bind_some] at executed
          exact ih middle (preserved selected before middle start reduced) executed

end
end VeriTile.Triton.FP.Structural.Interleaved
