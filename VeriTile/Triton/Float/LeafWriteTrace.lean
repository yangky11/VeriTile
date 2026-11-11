import VeriTile.Triton.Float.MemoryWriteTrace

/-! Named-region source leaves emit their actual evaluated primitive writes.
Unsupported pointer accesses and returned atomic values fail trace admission. -/
namespace VeriTile.Triton.FP.Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

def algWriteTraceSupported : Stmt → Prop
  | .assign .. => True
  | .store _ _ (.region ..) _ _ | .atomicAdd _ _ (.region ..) _ _ => True
  | .atomicRMW _ _ _ (.region ..) _ none _ none => True
  | _ => False

def algWriteEvents (M : Algebra α) : Stmt → State α → Option (List (MemoryWrite α))
  | .assign ..,_ => some []
  | .store _ _ (.region region offset) value mask,state => do
      storeEvents M region offset mask (← evalOp M none value state) state
  | .atomicAdd numeric _ (.region region offset) value mask,state => do
      atomicEvents M .add numeric region offset mask (← evalOp M none value state) state
  | .atomicRMW operation _ _ (.region region offset) value none mask none,state => do
      atomicReductionEvents M operation region offset mask (← evalOp M none value state) state
  | _,_ => none

theorem stepAlg_write_events (M : Algebra α) (statement : Stmt) (initial final : State α)
    (admitted : algWriteTraceSupported statement) (ran : stepAlg M statement initial = some final) :
    ∃ events, algWriteEvents M statement initial = some events ∧
      final.mem = (MemoryWrite.applyAll events initial).mem := by
  cases statement with
  | assign dtype shape register value =>
      obtain ⟨values,_,returned⟩ := Option.bind_eq_some_iff.mp ran
      have equal := Option.some.inj returned
      subst final
      exact ⟨[],rfl,rfl⟩
  | store dtype shape access value mask =>
      cases access with
      | ptr | blockPtr => simp [algWriteTraceSupported] at admitted
      | region region offset =>
          obtain ⟨values,evaluated,written⟩ := Option.bind_eq_some_iff.mp ran
          rw [store_region_events M region offset mask values initial] at written
          obtain ⟨events,generated,equal⟩ := Option.map_eq_some_iff.mp written
          refine ⟨events,?_,?_⟩
          · simp only [algWriteEvents,evaluated,generated,bind,Option.bind_some]
          · exact congrArg State.mem equal.symm
  | atomicAdd numeric shape access value mask =>
      cases access with
      | ptr | blockPtr => simp [algWriteTraceSupported] at admitted
      | region region offset =>
          obtain ⟨values,evaluated,written⟩ := Option.bind_eq_some_iff.mp ran
          rw [atomicAdd_region_events M numeric .add region offset mask values initial] at written
          obtain ⟨events,generated,equal⟩ := Option.map_eq_some_iff.mp written
          refine ⟨events,?_,?_⟩
          · simp only [algWriteEvents,evaluated,generated,bind,Option.bind_some]
          · exact congrArg State.mem equal.symm
  | atomicRMW operation dtype shape access value extra mask result =>
      cases extra with
      | some extra => simp [algWriteTraceSupported] at admitted
      | none =>
        cases result with
        | some result => simp [algWriteTraceSupported] at admitted
        | none =>
          cases access with
          | ptr | blockPtr => simp [algWriteTraceSupported] at admitted
          | region region offset =>
              obtain ⟨values,evaluated,written⟩ := Option.bind_eq_some_iff.mp ran
              rw [atomicReduction_region_events M operation region offset mask values initial] at written
              obtain ⟨events,generated,equal⟩ := Option.map_eq_some_iff.mp written
              refine ⟨events,?_,?_⟩
              · simp only [algWriteEvents,evaluated,generated,bind,Option.bind_some]
              · exact congrArg State.mem equal.symm
  | forLoop | forRange | forRangeDyn | forRangeInt | ifThen | ifThenElse => simp [algWriteTraceSupported] at admitted

#axiomsClean stepAlg_write_events

def leafWriteTraceSupported : ComputeStmt → Prop
  | .alg statement => algWriteTraceSupported statement
  | .assign .. => True
  | .store _ _ (.region ..) _ _ | .atomicAdd _ _ (.region ..) _ _ => True
  | .atomicRMW _ _ _ (.region ..) _ none _ none => True
  | _ => False

def leafWriteEvents (M : Algebra α) : ComputeStmt → State α → Option (List (MemoryWrite α))
  | .alg statement,state => algWriteEvents M statement state
  | .assign ..,_ => some []
  | .store _ _ (.region region offset) value mask,state => do
      storeEvents M region offset mask (← evalExpr M value state) state
  | .atomicAdd numeric _ (.region region offset) value mask,state => do
      atomicEvents M .add numeric region offset mask (← evalExpr M value state) state
  | .atomicRMW operation _ _ (.region region offset) value none mask none,state => do
      atomicReductionEvents M operation region offset mask (← evalExpr M value state) state
  | _,_ => none

theorem step_write_events (M : Algebra α) (statement : ComputeStmt) (initial final : State α)
    (admitted : leafWriteTraceSupported statement) (ran : step M statement initial = some final) :
    ∃ events, leafWriteEvents M statement initial = some events ∧
      final.mem = (MemoryWrite.applyAll events initial).mem := by
  cases statement with
  | alg statement =>
      exact stepAlg_write_events M statement initial final admitted (by simpa only [step] using ran)
  | assign dtype shape register value =>
      simp only [step] at ran
      obtain ⟨values,_,returned⟩ := Option.bind_eq_some_iff.mp ran
      have equal := Option.some.inj returned
      subst final
      exact ⟨[],rfl,rfl⟩
  | store dtype shape access value mask =>
      cases access with
      | ptr | blockPtr => simp [leafWriteTraceSupported] at admitted
      | region region offset =>
          simp only [step] at ran
          obtain ⟨values,evaluated,written⟩ := Option.bind_eq_some_iff.mp ran
          rw [store_region_events M region offset mask values initial] at written
          obtain ⟨events,generated,equal⟩ := Option.map_eq_some_iff.mp written
          refine ⟨events,?_,?_⟩
          · simp only [leafWriteEvents,evaluated,generated,bind,Option.bind_some]
          · exact congrArg State.mem equal.symm
  | atomicAdd numeric shape access value mask =>
      cases access with
      | ptr | blockPtr => simp [leafWriteTraceSupported] at admitted
      | region region offset =>
          simp only [step] at ran
          obtain ⟨values,evaluated,written⟩ := Option.bind_eq_some_iff.mp ran
          rw [atomicAdd_region_events M numeric .add region offset mask values initial] at written
          obtain ⟨events,generated,equal⟩ := Option.map_eq_some_iff.mp written
          refine ⟨events,?_,?_⟩
          · simp only [leafWriteEvents,evaluated,generated,bind,Option.bind_some]
          · exact congrArg State.mem equal.symm
  | atomicRMW operation dtype shape access value extra mask result =>
      cases extra with
      | some extra => simp [leafWriteTraceSupported] at admitted
      | none =>
        cases result with
        | some result => simp [leafWriteTraceSupported] at admitted
        | none =>
          cases access with
          | ptr | blockPtr => simp [leafWriteTraceSupported] at admitted
          | region region offset =>
              simp only [step] at ran
              obtain ⟨values,evaluated,written⟩ := Option.bind_eq_some_iff.mp ran
              rw [atomicReduction_region_events M operation region offset mask values initial] at written
              obtain ⟨events,generated,equal⟩ := Option.map_eq_some_iff.mp written
              refine ⟨events,?_,?_⟩
              · simp only [leafWriteEvents,evaluated,generated,bind,Option.bind_some]
              · exact congrArg State.mem equal.symm
  | forLoop | forRange | forRangeDyn | forRangeInt | ifThen | ifThenElse | effectMarker => simp [leafWriteTraceSupported] at admitted

#axiomsClean step_write_events

end
end VeriTile.Triton.FP.Structural
