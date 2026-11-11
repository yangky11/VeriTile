import VeriTile.Triton.Float.AtomicInterleaving
import VeriTile.Meta.StatementAudit

/-! Control-stack expansion and loop-index binding do not write shared memory. -/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

def leafHead : List Command → Bool
  | .source statement :: _ => leafSupported statement
  | _ => false

theorem Local.tick_control_memory (M : Algebra α) (before after : Local α) (memory : Memory α)
    (control : leafHead before.pending = false) (ran : before.tick M memory = some after) :
    after.state.mem = memory := by
  obtain ⟨code,state⟩ := before
  cases code with
  | nil => simp [tick] at ran
  | cons command rest =>
    cases command with
    | counted index current stop body =>
      by_cases active : current < stop <;> simp [tick,active] at ran <;> subst after <;> rfl
    | natural index current stop stride body | integer index current stop stride body =>
      by_cases inactive : stride = 0 ∨ stop ≤ current <;> simp [tick,inactive] at ran <;> subst after <;> rfl
    | source statement =>
      change leafSupported statement = false at control
      cases statement with
      | forLoop | forRange => simp [tick,leafSupported] at ran; subst after; rfl
      | forRangeDyn index start stop stride body | forRangeInt index start stop stride body =>
          cases firstRead : evalOp M none start { state with mem := memory } with
          | none => simp [tick,control,firstRead] at ran
          | some first =>
            cases lastRead : evalOp M none stop { state with mem := memory } with
            | none => simp [tick,control,firstRead,lastRead] at ran
            | some last =>
              cases strideRead : evalOp M none stride { state with mem := memory } with
              | none => simp [tick,control,firstRead,lastRead,strideRead] at ran
              | some delta =>
                  simp [tick,control,firstRead,lastRead,strideRead] at ran
                  subst after
                  rfl
      | ifThen condition body | ifThenElse condition yes no =>
          cases selected : evalOp M none condition { state with mem := memory } with
          | none => simp [tick,control,selected] at ran
          | some flag => simp [tick,control,selected] at ran; subst after; rfl
      | assign | store => simp [leafSupported] at control
      | atomicAdd | atomicRMW | alg | effectMarker => simp [tick,control] at ran

#axiomsClean Local.tick_control_memory
end
end VeriTile.Triton.FP.Structural.Interleaved
