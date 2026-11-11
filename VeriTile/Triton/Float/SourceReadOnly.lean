import VeriTile.Triton.Float.ReadFrame
import VeriTile.Triton.Float.AtomicInterleaving

/-! A structural read-only region check for ordinary source control. Only
named-region writes and discard-result atomics are accepted. Expressions have
no write effects; their read dependencies are checked separately. -/
namespace VeriTile.Triton.FP.Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

def accessOutside (regions : RegionName → Prop) : MemAccess dtype shape → Prop
  | .region region _ => ¬ regions (Region.cast region)
  | _ => False

def algReadOnly (regions : RegionName → Prop) : Stmt → Prop
  | .assign .. => True
  | .store _ _ access _ _ | .atomicAdd _ _ access _ _ => accessOutside regions access
  | .atomicRMW _ _ _ access _ none _ none => accessOutside regions access
  | _ => False

mutual
  def readOnly (regions : RegionName → Prop) : ComputeStmt → Prop
    | .alg statement => algReadOnly regions statement
    | .assign .. => True
    | .store _ _ access _ _ | .atomicAdd _ _ access _ _ => accessOutside regions access
    | .atomicRMW _ _ _ access _ none _ none => accessOutside regions access
    | .forLoop _ _ body | .forRange _ _ _ _ body | .forRangeDyn _ _ _ _ body |
      .forRangeInt _ _ _ _ body | .ifThen _ body => readOnlyBody regions body
    | .ifThenElse _ yes no => readOnlyBody regions yes ∧ readOnlyBody regions no
    | _ => False
  termination_by statement => sizeOf statement
  decreasing_by all_goals (simp_wf <;> omega)

  def readOnlyBody (regions : RegionName → Prop) : List ComputeStmt → Prop
    | [] => True
    | statement :: rest => readOnly regions statement ∧ readOnlyBody regions rest
  termination_by body => sizeOf body
  decreasing_by all_goals (simp_wf <;> omega)
end

theorem readOnlyBody_iff (regions : RegionName → Prop) (body : List ComputeStmt) :
    readOnlyBody regions body ↔ ∀ statement ∈ body, readOnly regions statement := by
  induction body with
  | nil => simp [readOnlyBody]
  | cons statement rest ih => simp [readOnlyBody,ih]

variable {α : Type} [Inhabited α]

theorem store_access_frame (M : Algebra α) {dtype : TileDType} {shape : TileShape}
    (regions : RegionName → Prop) (access : MemAccess dtype shape) (outside : accessOutside regions access)
    (mask : MaskOpt dtype shape) (values : Values α dtype shape)
    (initial final : State α) (ran : store M access mask values initial = some final) :
    final.AgreesOn regions initial := by
  cases access with
  | region region offset => exact store_region_frame M regions region outside offset mask values initial final ran
  | ptr | blockPtr => simp [accessOutside] at outside

theorem atomicAdd_access_frame (M : Algebra α) {dtype : TileDType} {shape : TileShape}
    (regions : RegionName → Prop) (numeric : NumericDType dtype) (access : MemAccess dtype shape)
    (outside : accessOutside regions access) (mask : MaskOpt dtype shape) (values : Values α dtype shape)
    (initial final : State α) (ran : atomicAdd M numeric access mask values initial = some final) :
    final.AgreesOn regions initial := by
  cases access with
  | region region offset => exact atomicAdd_region_frame M regions region outside numeric offset mask values initial final ran
  | ptr | blockPtr => simp [accessOutside] at outside

theorem atomicReduction_access_frame (M : Algebra α) (operation : RMWOp) {dtype : TileDType} {shape : TileShape}
    (regions : RegionName → Prop) (access : MemAccess dtype shape) (outside : accessOutside regions access)
    (mask : MaskOpt dtype shape) (values : Values α dtype shape)
    (initial final : State α) (ran : atomicReduction M operation access mask values initial = some final) :
    final.AgreesOn regions initial := by
  cases access with
  | region region offset => exact atomicReduction_region_frame M operation regions region outside offset mask values initial final ran
  | ptr | blockPtr => simp [accessOutside] at outside

theorem algReadOnly_frame (M : Algebra α) (regions : RegionName → Prop) (statement : Stmt)
    (confined : algReadOnly regions statement) (initial final : State α) (ran : stepAlg M statement initial = some final) :
    ∀ region, regions region → final.mem region = initial.mem region := by
  unfold stepAlg at ran
  split at ran
  · simp only [bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at ran
    obtain ⟨value,_,same⟩ := ran
    subst final
    intros; rfl
  · obtain ⟨value,_,executed⟩ := Option.bind_eq_some_iff.mp ran
    exact (store_access_frame M regions _ confined _ value initial final executed).memory
  · obtain ⟨value,_,executed⟩ := Option.bind_eq_some_iff.mp ran
    exact (atomicAdd_access_frame M regions _ _ confined _ value initial final executed).memory
  · obtain ⟨value,_,executed⟩ := Option.bind_eq_some_iff.mp ran
    exact (atomicReduction_access_frame M _ regions _ confined _ value initial final executed).memory
  · contradiction

theorem readOnly_leaf_frame (M : Algebra α) (regions : RegionName → Prop) (statement : ComputeStmt)
    (confined : readOnly regions statement) (supported : Interleaved.leafSupported statement = true)
    (initial final : State α) (ran : step M statement initial = some final) :
    ∀ region, regions region → final.mem region = initial.mem region := by
  cases statement with
  | alg statement =>
      simp only [step] at ran
      simp only [readOnly] at confined
      exact algReadOnly_frame M regions statement confined initial final ran
  | assign dtype shape name expression =>
      simp only [step,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at ran
      obtain ⟨value,_,same⟩ := ran
      subst final
      intros; rfl
  | store dtype shape memory expression mask =>
      simp only [step] at ran
      simp only [readOnly] at confined
      obtain ⟨value,_,executed⟩ := Option.bind_eq_some_iff.mp ran
      exact (store_access_frame M regions _ confined _ value initial final executed).memory
  | atomicAdd numeric shape memory expression mask =>
      simp only [step] at ran
      simp only [readOnly] at confined
      obtain ⟨value,_,executed⟩ := Option.bind_eq_some_iff.mp ran
      exact (atomicAdd_access_frame M regions _ _ confined _ value initial final executed).memory
  | atomicRMW operation dtype shape memory expression result mask order =>
      cases result <;> cases order <;> try { simp [Interleaved.leafSupported] at supported }
      simp only [step] at ran
      simp only [readOnly] at confined
      obtain ⟨value,_,executed⟩ := Option.bind_eq_some_iff.mp ran
      exact (atomicReduction_access_frame M _ regions _ confined _ value initial final executed).memory
  | forLoop | forRange | forRangeDyn | forRangeInt | ifThen | ifThenElse | effectMarker =>
      simp [Interleaved.leafSupported] at supported

#axiomsClean readOnlyBody_iff
#axiomsClean store_access_frame
#axiomsClean atomicAdd_access_frame
#axiomsClean atomicReduction_access_frame
#axiomsClean algReadOnly_frame
#axiomsClean readOnly_leaf_frame
end
end VeriTile.Triton.FP.Structural
