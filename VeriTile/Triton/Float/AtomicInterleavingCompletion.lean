import VeriTile.Triton.Float.AtomicInterleavingCorrect

/-! Completion witnesses for the statement-level scheduler. These lemmas
expand supported control flow into actual local ticks; a whole-program
execution is not installed as a scheduler callback. -/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {α : Type} [Inhabited α]

def Local.append (thread : Local α) (tail : List Command) : Local α :=
  ⟨thread.pending ++ tail,thread.state⟩

def Local.Advances (M : Algebra α) (before after : Local α) : Prop :=
  Relation.ReflTransGen (fun first last => first.tick M first.state.mem = some last) before after

theorem Local.Advances.single (M : Algebra α) {before after : Local α}
    (ran : before.tick M before.state.mem = some after) : before.Advances M after :=
  Relation.ReflTransGen.single ran

theorem Local.tick_append (M : Algebra α) (before after : Local α) (tail : List Command)
    (ran : before.tick M before.state.mem = some after) :
    (before.append tail).tick M before.state.mem = some (after.append tail) := by
  obtain ⟨code,state⟩ := before
  cases code with
  | nil => simp [tick] at ran
  | cons command rest =>
    cases command with
    | counted index current stop body =>
      by_cases active : current < stop <;> simp [tick,active] at ran <;> subst after <;>
        simp [append,tick,active,List.append_assoc]
    | natural index current stop stride body =>
      by_cases active : stride = 0 ∨ stop ≤ current <;> simp [tick,active] at ran <;> subst after <;>
        simp [append,tick,active,List.append_assoc]
    | integer index current stop stride body =>
      by_cases active : stride = 0 ∨ stop ≤ current <;> simp [tick,active] at ran <;> subst after <;>
        simp [append,tick,active,List.append_assoc]
    | source statement =>
      by_cases supported : leafSupported statement = true
      · cases advanced : step M statement state with
        | none => simp [tick,supported,advanced] at ran
        | some next =>
          simp [tick,supported,advanced] at ran
          subst after
          simp [append,tick,supported,advanced]
      · have unsupported : leafSupported statement = false := Bool.eq_false_of_not_eq_true supported
        cases statement with
        | forLoop index stop body =>
          simp [tick,leafSupported] at ran
          subst after
          simp [append,tick,leafSupported]
        | forRange index first last stride body =>
          simp [tick,leafSupported] at ran
          subst after
          simp [append,tick,leafSupported]
        | forRangeDyn index first last stride body =>
          cases firstRead : evalOp M none first state with
          | none => simp [tick,leafSupported,firstRead] at ran
          | some a =>
            cases lastRead : evalOp M none last state with
            | none => simp [tick,leafSupported,firstRead,lastRead] at ran
            | some b =>
              cases strideRead : evalOp M none stride state with
              | none => simp [tick,leafSupported,firstRead,lastRead,strideRead] at ran
              | some delta =>
                simp [tick,leafSupported,firstRead,lastRead,strideRead] at ran
                subst after
                simp [append,tick,leafSupported,firstRead,lastRead,strideRead]
        | forRangeInt index first last stride body =>
          cases firstRead : evalOp M none first state with
          | none => simp [tick,leafSupported,firstRead] at ran
          | some a =>
            cases lastRead : evalOp M none last state with
            | none => simp [tick,leafSupported,firstRead,lastRead] at ran
            | some b =>
              cases strideRead : evalOp M none stride state with
              | none => simp [tick,leafSupported,firstRead,lastRead,strideRead] at ran
              | some delta =>
                simp [tick,leafSupported,firstRead,lastRead,strideRead] at ran
                subst after
                simp [append,tick,leafSupported,firstRead,lastRead,strideRead]
        | ifThen condition body =>
          cases selected : evalOp M none condition state with
          | none => simp [tick,leafSupported,selected] at ran
          | some flag =>
            cases choice : flag () <;> simp [tick,leafSupported,selected,choice] at ran <;>
              subst after <;> simp [append,tick,leafSupported,selected,choice,List.append_assoc]
        | ifThenElse condition yes no =>
          cases selected : evalOp M none condition state with
          | none => simp [tick,leafSupported,selected] at ran
          | some flag =>
            cases choice : flag () <;> simp [tick,leafSupported,selected,choice] at ran <;>
              subst after <;> simp [append,tick,leafSupported,selected,choice,List.append_assoc]
        | assign => simp [leafSupported] at unsupported
        | store => simp [leafSupported] at unsupported
        | atomicAdd => simp [tick,unsupported] at ran
        | atomicRMW => simp [tick,unsupported] at ran
        | alg => simp [tick,unsupported] at ran
        | effectMarker => simp [tick,unsupported] at ran

theorem Local.Advances.append (M : Algebra α) {before after : Local α}
    (ran : before.Advances M after) (tail : List Command) :
    (before.append tail).Advances M (after.append tail) := by
  induction ran with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ tick ih => exact ih.tail (Local.tick_append M _ _ tail tick)

theorem Local.Advances.denotes (M : Algebra α) {before after : Local α}
    (ran : before.Advances M after) : evaluate M before.pending before.state = evaluate M after.pending after.state := by
  induction ran with
  | refl => rfl
  | tail _ tick ih => exact ih.trans (tick_denotes M _ _ _ tick)

#axiomsClean Local.tick_append
#axiomsClean Local.Advances.append
#axiomsClean Local.Advances.denotes
end
end VeriTile.Triton.FP.Structural.Interleaved
