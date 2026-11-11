import VeriTile.Triton.Float.AccessReadDependency

/-! Source expressions and control bounds declare their read regions. Together
with the independent write check, this gives local-state agreement even when
other, writable regions contain different values. -/
namespace VeriTile.Triton.FP.Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

def algDependencies (regions : RegionName → Prop) : Stmt → Prop
  | .assign _ _ _ expression => Reads regions expression
  | .store _ _ access expression mask | .atomicAdd _ _ access expression mask =>
      accessReads regions access ∧ maskReads regions mask ∧ Reads regions expression
  | .atomicRMW _ _ _ access expression none mask none =>
      accessReads regions access ∧ maskReads regions mask ∧ Reads regions expression
  | _ => False

mutual
  def readDependencies (regions : RegionName → Prop) : ComputeStmt → Prop
    | .alg statement => algDependencies regions statement
    | .assign _ _ _ expression => ExprReads regions expression
    | .store _ _ access expression mask | .atomicAdd _ _ access expression mask =>
        accessReads regions access ∧ maskReads regions mask ∧ ExprReads regions expression
    | .atomicRMW _ _ _ access expression none mask none =>
        accessReads regions access ∧ maskReads regions mask ∧ ExprReads regions expression
    | .forLoop _ _ body | .forRange _ _ _ _ body => bodyDependencies regions body
    | .forRangeDyn _ first last stride body | .forRangeInt _ first last stride body =>
        Reads regions first ∧ Reads regions last ∧ Reads regions stride ∧ bodyDependencies regions body
    | .ifThen condition body => Reads regions condition ∧ bodyDependencies regions body
    | .ifThenElse condition yes no => Reads regions condition ∧ bodyDependencies regions yes ∧ bodyDependencies regions no
    | _ => False
  termination_by statement => sizeOf statement
  decreasing_by all_goals (simp_wf <;> omega)

  def bodyDependencies (regions : RegionName → Prop) : List ComputeStmt → Prop
    | [] => True
    | statement :: rest => readDependencies regions statement ∧ bodyDependencies regions rest
  termination_by body => sizeOf body
  decreasing_by all_goals (simp_wf <;> omega)
end

theorem bodyDependencies_iff (regions : RegionName → Prop) (body : List ComputeStmt) :
    bodyDependencies regions body ↔ ∀ statement ∈ body, readDependencies regions statement := by
  induction body with
  | nil => simp [bodyDependencies]
  | cons statement rest ih => simp [bodyDependencies,ih]

variable {α : Type} [Inhabited α]

theorem algDependencies_agrees (M : Algebra α) (regions : RegionName → Prop) (statement : Stmt)
    (dependency : algDependencies regions statement) (confined : algReadOnly regions statement)
    (first second final : State α) (same : first.AgreesOn regions second)
    (ran : stepAlg M statement first = some final) :
    ∃ other, stepAlg M statement second = some other ∧ final.AgreesOn regions other := by
  unfold stepAlg at ran
  split at ran
  · simp only [bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at ran
    obtain ⟨value,read,returned⟩ := ran
    have otherRead := (Reads.eval_eq dependency M none first second same).symm.trans read
    subst final
    refine ⟨second.setReg _ _ _ value,?_,same.setReg _ _ _ value⟩
    simp [stepAlg,otherRead]
  · obtain ⟨value,read,executed⟩ := Option.bind_eq_some_iff.mp ran
    have otherRead := (Reads.eval_eq dependency.2.2 M none first second same).symm.trans read
    obtain ⟨other,stored,related⟩ := store_agrees M regions _ _ dependency.1 dependency.2.1 confined value first second final same executed
    exact ⟨other,by simpa [stepAlg,otherRead] using stored,related⟩
  · obtain ⟨value,read,executed⟩ := Option.bind_eq_some_iff.mp ran
    have otherRead := (Reads.eval_eq dependency.2.2 M none first second same).symm.trans read
    obtain ⟨other,stored,related⟩ := atomicAdd_agrees M regions _ _ _ dependency.1 dependency.2.1 confined value first second final same executed
    exact ⟨other,by simpa [stepAlg,otherRead] using stored,related⟩
  · obtain ⟨value,read,executed⟩ := Option.bind_eq_some_iff.mp ran
    have otherRead := (Reads.eval_eq dependency.2.2 M none first second same).symm.trans read
    obtain ⟨other,stored,related⟩ := atomicReduction_agrees M _ regions _ _ dependency.1 dependency.2.1 confined value first second final same executed
    exact ⟨other,by simpa [stepAlg,otherRead] using stored,related⟩
  · contradiction

theorem readDependencies_leaf_agrees (M : Algebra α) (regions : RegionName → Prop) (statement : ComputeStmt)
    (dependency : readDependencies regions statement) (confined : readOnly regions statement)
    (supported : Interleaved.leafSupported statement = true)
    (first second final : State α) (same : first.AgreesOn regions second)
    (ran : step M statement first = some final) :
    ∃ other, step M statement second = some other ∧ final.AgreesOn regions other := by
  cases statement with
  | alg statement =>
      simp only [step] at ran ⊢
      simp only [readOnly] at confined
      simp only [readDependencies] at dependency
      exact algDependencies_agrees M regions statement dependency confined first second final same ran
  | assign dtype shape name expression =>
      simp only [step,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at ran
      simp only [readDependencies] at dependency
      obtain ⟨value,read,returned⟩ := ran
      have otherRead := (ExprReads.eval_eq dependency M first second same).symm.trans read
      subst final
      exact ⟨second.setReg name dtype shape value,by simp [step,otherRead],same.setReg name dtype shape value⟩
  | store dtype shape access expression mask =>
      simp only [step] at ran
      simp only [readDependencies] at dependency
      simp only [readOnly] at confined
      obtain ⟨value,read,executed⟩ := Option.bind_eq_some_iff.mp ran
      have otherRead := (ExprReads.eval_eq dependency.2.2 M first second same).symm.trans read
      obtain ⟨other,stored,related⟩ := store_agrees M regions _ _ dependency.1 dependency.2.1 confined value first second final same executed
      exact ⟨other,by simpa [step,otherRead] using stored,related⟩
  | atomicAdd numeric shape access expression mask =>
      simp only [step] at ran
      simp only [readDependencies] at dependency
      simp only [readOnly] at confined
      obtain ⟨value,read,executed⟩ := Option.bind_eq_some_iff.mp ran
      have otherRead := (ExprReads.eval_eq dependency.2.2 M first second same).symm.trans read
      obtain ⟨other,stored,related⟩ := atomicAdd_agrees M regions _ _ _ dependency.1 dependency.2.1 confined value first second final same executed
      exact ⟨other,by simpa [step,otherRead] using stored,related⟩
  | atomicRMW operation dtype shape access expression result mask order =>
      cases result <;> cases order <;> try { simp [Interleaved.leafSupported] at supported }
      simp only [step] at ran
      simp only [readDependencies] at dependency
      simp only [readOnly] at confined
      obtain ⟨value,read,executed⟩ := Option.bind_eq_some_iff.mp ran
      have otherRead := (ExprReads.eval_eq dependency.2.2 M first second same).symm.trans read
      obtain ⟨other,stored,related⟩ := atomicReduction_agrees M _ regions _ _ dependency.1 dependency.2.1 confined value first second final same executed
      exact ⟨other,by simpa [step,otherRead] using stored,related⟩
  | forLoop | forRange | forRangeDyn | forRangeInt | ifThen | ifThenElse | effectMarker =>
      simp [Interleaved.leafSupported] at supported

#axiomsClean bodyDependencies_iff
#axiomsClean algDependencies_agrees
#axiomsClean readDependencies_leaf_agrees
end
end VeriTile.Triton.FP.Structural
