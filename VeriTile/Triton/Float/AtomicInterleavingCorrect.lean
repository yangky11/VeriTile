import VeriTile.Triton.Float.AtomicInterleaving
import VeriTile.Meta.StatementAudit

/-! The interleaving control stack denotes the existing Structural source
semantics for each individual invocation. Scheduling adds shared-state choices;
it does not replace any source expression or loop with a supplied formula. -/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def Command.eval {α : Type} [Inhabited α] (M : Algebra α) : Command → State α → Option (State α)
  | .source statement, state => step M statement state
  | .counted index current stop body, state => loop M index current stop body state
  | .natural index current stop stride body, state => range M index current stop stride body state
  | .integer index current stop stride body, state => rangeInt M index current stop stride body state

def evaluate {α : Type} [Inhabited α] (M : Algebra α) : List Command → State α → Option (State α)
  | [], state => some state
  | command :: rest, state => (command.eval M state).bind (evaluate M rest)

theorem evaluate_commands {α : Type} [Inhabited α] (M : Algebra α)
    (body : List ComputeStmt) (state : State α) : evaluate M (commands body) state = Structural.run M body state := by
  induction body generalizing state with
  | nil => simp [commands,evaluate,Structural.run]
  | cons statement rest ih =>
      simp only [commands,List.map_cons,evaluate,Command.eval,Structural.run]
      cases step M statement state with
      | none => rfl
      | some next => exact ih next

theorem evaluate_append {α : Type} [Inhabited α] (M : Algebra α)
    (first rest : List Command) (state : State α) :
    evaluate M (first ++ rest) state = (evaluate M first state).bind (evaluate M rest) := by
  induction first generalizing state with
  | nil => rfl
  | cons command tail ih =>
      simp only [List.cons_append,evaluate]
      cases command.eval M state <;> simp [ih]

theorem evaluate_body {α : Type} [Inhabited α] (M : Algebra α)
    (body : List ComputeStmt) (rest : List Command) (state : State α) :
    evaluate M (commands body ++ rest) state = (Structural.run M body state).bind (evaluate M rest) := by
  rw [evaluate_append,evaluate_commands]

/-- Every successful tick preserves the individual invocation's Structural
continuation result. The interleaving may change shared memory between ticks;
this lemma asserts no equality between different interleavings. -/
theorem tick_denotes {α : Type} [Inhabited α] (M : Algebra α)
    (code : List Command) (state : State α) (after : Local α)
    (executed : (Local.mk code state).tick M state.mem = some after) :
    evaluate M code state = evaluate M after.pending after.state := by
  cases code with
  | nil => simp [Local.tick] at executed
  | cons command rest =>
    cases command with
    | counted index current stop body =>
      by_cases active : current < stop
      · simp [Local.tick,active] at executed
        subst after
        rw [evaluate,Command.eval,loop]
        simp only [active,ite_true,evaluate_body,evaluate,Command.eval]
        exact Option.bind_assoc _ _ _
      · simp [Local.tick,active] at executed
        subst after
        simp [evaluate,Command.eval,loop,active]
    | natural index current stop stride body =>
      by_cases zero : stride = 0
      · simp [Local.tick,zero] at executed
        subst after
        simp [evaluate,Command.eval,range,zero]
      · by_cases active : current < stop
        · simp [Local.tick,zero,Nat.not_le.mpr active] at executed
          subst after
          rw [evaluate,Command.eval,range]
          simp only [zero,active,ite_false,ite_true,evaluate_body,evaluate,Command.eval]
          exact Option.bind_assoc _ _ _
        · simp [Local.tick,zero,Nat.le_of_not_gt active] at executed
          subst after
          simp [evaluate,Command.eval,range,zero,active]
    | integer index current stop stride body =>
      by_cases zero : stride = 0
      · simp [Local.tick,zero] at executed
        subst after
        simp [evaluate,Command.eval,rangeInt,zero]
      · by_cases active : current < stop
        · simp [Local.tick,zero,Int.not_le.mpr active] at executed
          subst after
          rw [evaluate,Command.eval,rangeInt]
          simp only [zero,active,ite_false,ite_true,evaluate_body,evaluate,Command.eval]
          exact Option.bind_assoc _ _ _
        · simp [Local.tick,zero,Int.le_of_not_gt active] at executed
          subst after
          simp [evaluate,Command.eval,rangeInt,zero,active]
    | source statement =>
      by_cases supported : leafSupported statement = true
      · have lifted : (step M statement state).bind (fun next => some (Local.mk rest next)) = some after := by
          simp only [Local.tick,supported,ite_true] at executed
          change (step M statement state).bind (fun next => some (Local.mk rest next)) = some after at executed
          exact executed
        obtain ⟨next,advanced,returned⟩ := Option.bind_eq_some_iff.mp lifted
        have same := Option.some.inj returned
        subst after
        simp only [evaluate,Command.eval,advanced,Option.bind_some]
      · have unsupported : leafSupported statement = false := Bool.eq_false_of_not_eq_true supported
        cases statement with
        | forLoop index stop body =>
          simp [Local.tick,leafSupported] at executed
          subst after
          simp [evaluate,Command.eval,step]
        | forRange index first last stride body =>
          simp [Local.tick,leafSupported] at executed
          subst after
          simp [evaluate,Command.eval,step]
        | forRangeDyn index first last stride body =>
          cases firstRead : evalOp M none first state with
          | none => simp [Local.tick,leafSupported,firstRead] at executed
          | some a =>
            cases lastRead : evalOp M none last state with
            | none => simp [Local.tick,leafSupported,firstRead,lastRead] at executed
            | some b =>
              cases strideRead : evalOp M none stride state with
              | none => simp [Local.tick,leafSupported,firstRead,lastRead,strideRead] at executed
              | some delta =>
                simp [Local.tick,leafSupported,firstRead,lastRead,strideRead] at executed
                subst after
                simp [evaluate,Command.eval,step,firstRead,lastRead,strideRead]
        | forRangeInt index first last stride body =>
          cases firstRead : evalOp M none first state with
          | none => simp [Local.tick,leafSupported,firstRead] at executed
          | some a =>
            cases lastRead : evalOp M none last state with
            | none => simp [Local.tick,leafSupported,firstRead,lastRead] at executed
            | some b =>
              cases strideRead : evalOp M none stride state with
              | none => simp [Local.tick,leafSupported,firstRead,lastRead,strideRead] at executed
              | some delta =>
                simp [Local.tick,leafSupported,firstRead,lastRead,strideRead] at executed
                subst after
                simp [evaluate,Command.eval,step,firstRead,lastRead,strideRead]
        | ifThen condition body =>
          cases selected : evalOp M none condition state with
          | none => simp [Local.tick,leafSupported,selected] at executed
          | some flag =>
            cases choice : flag () <;> simp [Local.tick,leafSupported,selected,choice] at executed <;>
              subst after <;> simp [evaluate,Command.eval,step,selected,choice,evaluate_body]
        | ifThenElse condition yes no =>
          cases selected : evalOp M none condition state with
          | none => simp [Local.tick,leafSupported,selected] at executed
          | some flag =>
            cases choice : flag () <;> simp [Local.tick,leafSupported,selected,choice] at executed <;>
              subst after <;> simp [evaluate,Command.eval,step,selected,choice,evaluate_body]
        | assign => simp [leafSupported] at unsupported
        | store => simp [leafSupported] at unsupported
        | atomicAdd => simp [Local.tick,unsupported] at executed
        | atomicRMW => simp [Local.tick,unsupported] at executed
        | alg => simp [Local.tick,unsupported] at executed
        | effectMarker => simp [Local.tick,unsupported] at executed

#axiomsClean tick_denotes
#axiomsClean tick_preserves_other_local
#axiomsClean run_invariant

#axiomsClean evaluate_commands
#axiomsClean evaluate_append
#axiomsClean evaluate_body
end
end VeriTile.Triton.FP.Structural.Interleaved
