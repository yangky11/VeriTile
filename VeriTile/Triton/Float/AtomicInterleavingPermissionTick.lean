import VeriTile.Triton.Float.AtomicInterleavingTracePermission
import VeriTile.Triton.Float.AtomicInterleavingPermission

/-! Every actual source tick preserves the continuation's source write permissions. -/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {α : Type} [Inhabited α]

theorem tick_tracePermission (M : Algebra α) (ordinary atomic : RegionName → Nat → Prop)
    (code : List Command) (state : State α) (after : Local α)
    (safe : evaluatePermitted M ordinary atomic code state)
    (executed : (Local.mk code state).tick M state.mem = some after) :
    (Local.mk code state).Permitted M ordinary atomic state.mem ∧ evaluatePermitted M ordinary atomic after.pending after.state := by
  cases code with
  | nil => simp [Local.tick] at executed
  | cons command rest =>
    simp only [evaluatePermitted,Command.Permissions,Command.eval] at safe
    cases command with
    | counted index current stop body =>
      dsimp only at safe
      by_cases active : current < stop
      · simp [Local.tick,active] at executed
        subst after
        refine ⟨trivial,?_⟩
        rw [Permission.counted,loop] at safe
        simp only [active,ite_true] at safe
        apply (evaluatePermitted_body M ordinary atomic _ _ _).mpr
        refine ⟨safe.1.1,?_⟩
        intro middle bodyRun
        refine ⟨?_,?_⟩
        · simpa only [Command.Permissions,bodyRun] using safe.1.2
        · intro final restRun
          apply safe.2 final
          simpa only [bodyRun,Option.bind_some,bind,Command.eval] using restRun
      · simp [Local.tick,active] at executed
        subst after
        exact ⟨trivial,safe.2 state (by simp [Command.eval,loop,active])⟩
    | natural index current stop stride body =>
      dsimp only at safe
      by_cases inactive : stride = 0 ∨ stop ≤ current
      · simp [Local.tick,inactive] at executed
        subst after
        refine ⟨trivial,safe.2 state ?_⟩
        rcases inactive with zero | past
        · simp [Command.eval,range,zero]
        · simp [Command.eval,range,Nat.not_lt.mpr past]
      · have nonzero : stride ≠ 0 := fun zero => inactive (Or.inl zero)
        have active : current < stop := Nat.lt_of_not_ge (fun past => inactive (Or.inr past))
        simp [Local.tick,inactive] at executed
        subst after
        refine ⟨trivial,?_⟩
        rw [Permission.natural,range] at safe
        simp only [nonzero,active,ite_false,ite_true] at safe
        apply (evaluatePermitted_body M ordinary atomic _ _ _).mpr
        refine ⟨safe.1.1,?_⟩
        intro middle bodyRun
        refine ⟨?_,?_⟩
        · simpa only [Command.Permissions,bodyRun] using safe.1.2
        · intro final restRun
          apply safe.2 final
          simpa only [bodyRun,Option.bind_some,bind,Command.eval] using restRun
    | integer index current stop stride body =>
      dsimp only at safe
      by_cases inactive : stride = 0 ∨ stop ≤ current
      · simp [Local.tick,inactive] at executed
        subst after
        refine ⟨trivial,safe.2 state ?_⟩
        rcases inactive with zero | past
        · simp [Command.eval,rangeInt,zero]
        · simp [Command.eval,rangeInt,Int.not_lt.mpr past]
      · have nonzero : stride ≠ 0 := fun zero => inactive (Or.inl zero)
        have active : current < stop := Int.lt_of_not_ge (fun past => inactive (Or.inr past))
        simp [Local.tick,inactive] at executed
        subst after
        refine ⟨trivial,?_⟩
        rw [Permission.integer,rangeInt] at safe
        simp only [nonzero,active,ite_false,ite_true] at safe
        apply (evaluatePermitted_body M ordinary atomic _ _ _).mpr
        refine ⟨safe.1.1,?_⟩
        intro middle bodyRun
        refine ⟨?_,?_⟩
        · simpa only [Command.Permissions,bodyRun] using safe.1.2
        · intro final restRun
          apply safe.2 final
          simpa only [bodyRun,Option.bind_some,bind,Command.eval] using restRun
    | source statement =>
      dsimp only at safe
      by_cases supported : leafSupported statement = true
      · cases advanced : step M statement state with
        | none => simp [Local.tick,supported,advanced] at executed
        | some next =>
          simp [Local.tick,supported,advanced] at executed
          subst after
          refine ⟨?_,safe.2 next advanced⟩
          cases statement <;> simp_all [Local.Permitted,leafSupported,Permission.statement]
      · have unsupported : leafSupported statement = false := Bool.eq_false_of_not_eq_true supported
        cases statement with
        | forLoop index stop body =>
          simp [Local.tick,leafSupported] at executed
          subst after
          refine ⟨trivial,?_⟩
          simpa only [evaluatePermitted,Command.Permissions,Command.eval,Permission.statement,step] using safe
        | forRange index start stop stride body =>
          simp [Local.tick,leafSupported] at executed
          subst after
          refine ⟨trivial,?_⟩
          simpa only [evaluatePermitted,Command.Permissions,Command.eval,Permission.statement,step] using safe
        | forRangeDyn index start stop stride body =>
          cases startRead : evalOp M none start state with
          | none => simp [Local.tick,leafSupported,startRead] at executed
          | some first =>
            cases stopRead : evalOp M none stop state with
            | none => simp [Local.tick,leafSupported,startRead,stopRead] at executed
            | some last =>
              cases strideRead : evalOp M none stride state with
              | none => simp [Local.tick,leafSupported,startRead,stopRead,strideRead] at executed
              | some delta =>
                simp [Local.tick,leafSupported,startRead,stopRead,strideRead] at executed
                subst after
                simp only [Permission.statement,step,startRead,stopRead,strideRead,bind,Option.bind_some] at safe
                exact ⟨trivial,safe.1,safe.2⟩
        | forRangeInt index start stop stride body =>
          cases startRead : evalOp M none start state with
          | none => simp [Local.tick,leafSupported,startRead] at executed
          | some first =>
            cases stopRead : evalOp M none stop state with
            | none => simp [Local.tick,leafSupported,startRead,stopRead] at executed
            | some last =>
              cases strideRead : evalOp M none stride state with
              | none => simp [Local.tick,leafSupported,startRead,stopRead,strideRead] at executed
              | some delta =>
                simp [Local.tick,leafSupported,startRead,stopRead,strideRead] at executed
                subst after
                simp only [Permission.statement,step,startRead,stopRead,strideRead,bind,Option.bind_some] at safe
                exact ⟨trivial,safe.1,safe.2⟩
        | ifThen condition body =>
          cases selected : evalOp M none condition state with
          | none => simp [Local.tick,leafSupported,selected] at executed
          | some flag =>
            cases choice : flag () <;> simp [Local.tick,leafSupported,selected,choice] at executed <;> subst after
            · simp only [Permission.statement,step,selected,choice,bind,Option.bind_some,Bool.false_eq_true,ite_false] at safe
              exact ⟨trivial,safe.2 state rfl⟩
            · simp only [Permission.statement,step,selected,choice,bind,Option.bind_some,ite_true] at safe
              exact ⟨trivial,(evaluatePermitted_body M ordinary atomic _ _ _).mpr ⟨safe.1,safe.2⟩⟩
        | ifThenElse condition yes no =>
          cases selected : evalOp M none condition state with
          | none => simp [Local.tick,leafSupported,selected] at executed
          | some flag =>
            cases choice : flag () <;> simp [Local.tick,leafSupported,selected,choice] at executed <;> subst after
            · simp only [Permission.statement,step,selected,choice,bind,Option.bind_some,Bool.false_eq_true,ite_false] at safe
              exact ⟨trivial,(evaluatePermitted_body M ordinary atomic _ _ _).mpr ⟨safe.1,safe.2⟩⟩
            · simp only [Permission.statement,step,selected,choice,bind,Option.bind_some,ite_true] at safe
              exact ⟨trivial,(evaluatePermitted_body M ordinary atomic _ _ _).mpr ⟨safe.1,safe.2⟩⟩
        | assign | store => simp [leafSupported] at unsupported
        | atomicAdd | atomicRMW | alg | effectMarker => simp [Local.tick,unsupported] at executed

#axiomsClean tick_tracePermission
end
end VeriTile.Triton.FP.Structural.Interleaved
