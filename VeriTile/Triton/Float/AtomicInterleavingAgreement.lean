import VeriTile.Triton.Float.AtomicInterleavingDependencies

/-! A source tick cannot observe changes outside its certified read regions.
Discard-result atomics retain their real destination writes, so agreement here
covers control and registers, not atomic destination equality. -/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {α : Type} [Inhabited α]

theorem tick_agrees (M : Algebra α) (regions : RegionName → Prop) (code : List Command)
    (confined : pendingReadOnly regions code) (dependent : pendingDependencies regions code)
    (first second : State α) (same : first.AgreesOn regions second) (final : Local α)
    (ran : (Local.mk code first).tick M first.mem = some final) :
    ∃ other, (Local.mk code second).tick M second.mem = some other ∧
      final.pending = other.pending ∧ final.state.AgreesOn regions other.state := by
  cases code with
  | nil => simp [Local.tick] at ran
  | cons command rest =>
    have headConfined := (pendingReadOnly_cons regions command rest).mp confined |>.1
    have headDependency := (pendingDependencies_cons regions command rest).mp dependent |>.1
    cases command with
    | counted index current stop body =>
      by_cases active : current < stop
      · simp [Local.tick,active] at ran
        subst final
        exact ⟨⟨_,second.setReg index .nat [] (fun _ => current)⟩,by simp [Local.tick,active],rfl,same.setReg _ _ _ _⟩
      · simp [Local.tick,active] at ran
        subst final
        exact ⟨⟨_,second⟩,by simp [Local.tick,active],rfl,same⟩
    | natural index current stop stride body =>
      by_cases inactive : stride = 0 ∨ stop ≤ current
      · simp [Local.tick,inactive] at ran
        subst final
        exact ⟨⟨_,second⟩,by simp [Local.tick,inactive],rfl,same⟩
      · simp [Local.tick,inactive] at ran
        subst final
        exact ⟨⟨_,second.setReg index .nat [] (fun _ => current)⟩,by simp [Local.tick,inactive],rfl,same.setReg _ _ _ _⟩
    | integer index current stop stride body =>
      by_cases inactive : stride = 0 ∨ stop ≤ current
      · simp [Local.tick,inactive] at ran
        subst final
        exact ⟨⟨_,second⟩,by simp [Local.tick,inactive],rfl,same⟩
      · simp [Local.tick,inactive] at ran
        subst final
        exact ⟨⟨_,second.setReg index .int [] (fun _ => current)⟩,by simp [Local.tick,inactive],rfl,same.setReg _ _ _ _⟩
    | source statement =>
      by_cases supported : leafSupported statement = true
      · cases advanced : step M statement first with
        | none => simp [Local.tick,supported,advanced] at ran
        | some next =>
          simp [Local.tick,supported,advanced] at ran
          subst final
          obtain ⟨other,executed,related⟩ := readDependencies_leaf_agrees M regions statement
            headDependency headConfined supported first second next same advanced
          exact ⟨⟨rest,other⟩,by simp [Local.tick,supported,executed],rfl,related⟩
      · have unsupported : leafSupported statement = false := Bool.eq_false_of_not_eq_true supported
        cases statement with
        | forLoop index stop body =>
          simp [Local.tick,leafSupported] at ran
          subst final
          exact ⟨⟨_,second⟩,by simp [Local.tick,leafSupported],rfl,same⟩
        | forRange index start stop stride body =>
          simp [Local.tick,leafSupported] at ran
          subst final
          exact ⟨⟨_,second⟩,by simp [Local.tick,leafSupported],rfl,same⟩
        | forRangeDyn index start stop stride body =>
          simp only [commandDependencies,readDependencies] at headDependency
          have starts := headDependency.1.eval_eq M none first second same
          have stops := headDependency.2.1.eval_eq M none first second same
          have strides := headDependency.2.2.1.eval_eq M none first second same
          cases startRead : evalOp M none start first with
          | none => simp [Local.tick,leafSupported,startRead] at ran
          | some startValue =>
            cases stopRead : evalOp M none stop first with
            | none => simp [Local.tick,leafSupported,startRead,stopRead] at ran
            | some stopValue =>
              cases strideRead : evalOp M none stride first with
              | none => simp [Local.tick,leafSupported,startRead,stopRead,strideRead] at ran
              | some strideValue =>
                simp [Local.tick,leafSupported,startRead,stopRead,strideRead] at ran
                subst final
                exact ⟨⟨_,second⟩,by simp [Local.tick,leafSupported,← starts,← stops,← strides,startRead,stopRead,strideRead],rfl,same⟩
        | forRangeInt index start stop stride body =>
          simp only [commandDependencies,readDependencies] at headDependency
          have starts := headDependency.1.eval_eq M none first second same
          have stops := headDependency.2.1.eval_eq M none first second same
          have strides := headDependency.2.2.1.eval_eq M none first second same
          cases startRead : evalOp M none start first with
          | none => simp [Local.tick,leafSupported,startRead] at ran
          | some startValue =>
            cases stopRead : evalOp M none stop first with
            | none => simp [Local.tick,leafSupported,startRead,stopRead] at ran
            | some stopValue =>
              cases strideRead : evalOp M none stride first with
              | none => simp [Local.tick,leafSupported,startRead,stopRead,strideRead] at ran
              | some strideValue =>
                simp [Local.tick,leafSupported,startRead,stopRead,strideRead] at ran
                subst final
                exact ⟨⟨_,second⟩,by simp [Local.tick,leafSupported,← starts,← stops,← strides,startRead,stopRead,strideRead],rfl,same⟩
        | ifThen condition body =>
          simp only [commandDependencies,readDependencies] at headDependency
          have equal := headDependency.1.eval_eq M none first second same
          cases selected : evalOp M none condition first with
          | none => simp [Local.tick,leafSupported,selected] at ran
          | some flag =>
            simp [Local.tick,leafSupported,selected] at ran
            subst final
            exact ⟨⟨_,second⟩,by simp [Local.tick,leafSupported,← equal,selected],rfl,same⟩
        | ifThenElse condition yes no =>
          simp only [commandDependencies,readDependencies] at headDependency
          have equal := headDependency.1.eval_eq M none first second same
          cases selected : evalOp M none condition first with
          | none => simp [Local.tick,leafSupported,selected] at ran
          | some flag =>
            simp [Local.tick,leafSupported,selected] at ran
            subst final
            exact ⟨⟨_,second⟩,by simp [Local.tick,leafSupported,← equal,selected],rfl,same⟩
        | assign => simp [leafSupported] at unsupported
        | store => simp [leafSupported] at unsupported
        | atomicAdd => simp [Local.tick,unsupported] at ran
        | atomicRMW => simp [Local.tick,unsupported] at ran
        | alg => simp [Local.tick,unsupported] at ran
        | effectMarker => simp [Local.tick,unsupported] at ran

#axiomsClean tick_agrees
end
end VeriTile.Triton.FP.Structural.Interleaved
