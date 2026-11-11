import VeriTile.Triton.Float.WritePermission

/-! Leaf write permissions separate ordinary and atomic footprints. Source
control is checked at its scheduled leaves; unsupported effects fail closed. -/
namespace VeriTile.Triton.FP.Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

def algWritePermitted (M : Algebra α) (ordinary atomic : RegionName → Nat → Prop)
    (statement : Stmt) (state : State α) : Prop :=
  match statement with
  | .assign .. => True
  | .store _ _ access _ mask => writePermitted M ordinary access mask state
  | .atomicAdd _ _ access _ mask => writePermitted M atomic access mask state
  | .atomicRMW operation _ _ access _ none mask none =>
      writePermitted { M with atomicAdd := M.atomicReduce operation } atomic access mask state
  | _ => False

def leafWritePermitted (M : Algebra α) (ordinary atomic : RegionName → Nat → Prop)
    (statement : ComputeStmt) (state : State α) : Prop :=
  match statement with
  | .alg statement => algWritePermitted M ordinary atomic statement state
  | .assign .. => True
  | .store _ _ access _ mask => writePermitted M ordinary access mask state
  | .atomicAdd _ _ access _ mask => writePermitted M atomic access mask state
  | .atomicRMW operation _ _ access _ none mask none =>
      writePermitted { M with atomicAdd := M.atomicReduce operation } atomic access mask state
  | _ => False

theorem algWritePermitted_frame (M : Algebra α) (ordinary atomic : RegionName → Nat → Prop)
    (statement : Stmt) (initial final : State α)
    (permitted : algWritePermitted M ordinary atomic statement initial)
    (ran : stepAlg M statement initial = some final) :
    final.CellsAgree (fun region offset => ¬ ordinary region offset ∧ ¬ atomic region offset) initial := by
  unfold stepAlg at ran
  split at ran
  · simp only [bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at ran
    obtain ⟨value,_,returned⟩ := ran
    subst final
    intro _ _ _
    rfl
  · obtain ⟨value,_,stored⟩ := Option.bind_eq_some_iff.mp ran
    intro region offset outside
    exact store_permission_frame M ordinary _ _ value initial final permitted stored region offset outside.1
  · obtain ⟨value,_,stored⟩ := Option.bind_eq_some_iff.mp ran
    intro region offset outside
    exact atomicAdd_permission_frame M atomic _ _ _ value initial final permitted stored region offset outside.2
  · obtain ⟨value,_,stored⟩ := Option.bind_eq_some_iff.mp ran
    intro region offset outside
    exact atomicReduction_permission_frame M _ atomic _ _ value initial final permitted stored region offset outside.2
  · contradiction

theorem leafWritePermitted_frame (M : Algebra α) (ordinary atomic : RegionName → Nat → Prop)
    (statement : ComputeStmt) (initial final : State α)
    (permitted : leafWritePermitted M ordinary atomic statement initial)
    (supported : Interleaved.leafSupported statement = true)
    (ran : step M statement initial = some final) :
    final.CellsAgree (fun region offset => ¬ ordinary region offset ∧ ¬ atomic region offset) initial := by
  cases statement with
  | alg statement =>
      simp only [step] at ran
      exact algWritePermitted_frame M ordinary atomic statement initial final permitted ran
  | assign dtype shape name expression =>
      simp only [step,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at ran
      obtain ⟨value,_,returned⟩ := ran
      subst final
      intro _ _ _
      rfl
  | store dtype shape access expression mask =>
      simp only [step] at ran
      obtain ⟨value,_,stored⟩ := Option.bind_eq_some_iff.mp ran
      intro region offset outside
      exact store_permission_frame M ordinary _ _ value initial final permitted stored region offset outside.1
  | atomicAdd dtype shape access expression mask =>
      simp only [step] at ran
      obtain ⟨value,_,stored⟩ := Option.bind_eq_some_iff.mp ran
      intro region offset outside
      exact atomicAdd_permission_frame M atomic _ _ _ value initial final permitted stored region offset outside.2
  | atomicRMW operation dtype shape access expression result mask order =>
      cases result <;> cases order <;> try { simp [Interleaved.leafSupported] at supported }
      simp only [step] at ran
      obtain ⟨value,_,stored⟩ := Option.bind_eq_some_iff.mp ran
      intro region offset outside
      exact atomicReduction_permission_frame M _ atomic _ _ value initial final permitted stored region offset outside.2
  | forLoop | forRange | forRangeDyn | forRangeInt | ifThen | ifThenElse | effectMarker =>
      simp [Interleaved.leafSupported] at supported

#axiomsClean algWritePermitted_frame
#axiomsClean leafWritePermitted_frame
end
end VeriTile.Triton.FP.Structural
