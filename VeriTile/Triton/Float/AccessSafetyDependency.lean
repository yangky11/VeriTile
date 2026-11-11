import VeriTile.Triton.Float.SafetyReadDependency
import VeriTile.Triton.Float.SourceReadDependency

/-! Address bounds and active masks are unchanged by memory interference
outside the source's structural input dependencies. -/
namespace VeriTile.Triton.FP.Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

theorem accessReads_safe_iff (dependency : accessReads regions access) (M : Algebra α)
    (precision : Option ComputeDType) (bounds : RegionName → Nat)
    (first second : State α) (same : first.AgreesOn regions second) :
    Safety.safeAddress M precision bounds first access ↔ Safety.safeAddress M precision bounds second access := by
  cases access with
  | region region offset => exact Reads.safe_iff dependency M precision bounds first second same
  | ptr | blockPtr => simp [accessReads] at dependency

theorem maskReads_safe_iff (dependency : maskReads regions mask) (M : Algebra α)
    (precision : Option ComputeDType) (bounds : RegionName → Nat)
    (first second : State α) (same : first.AgreesOn regions second) :
    Safety.safeMask M precision bounds first mask ↔ Safety.safeMask M precision bounds second mask := by
  cases mask with
  | none => rfl
  | mask condition => exact Reads.safe_iff dependency M precision bounds first second same
  | maskOther condition other =>
      exact and_congr (dependency.1.safe_iff M precision bounds first second same)
        (dependency.2.safe_iff M precision bounds first second same)

theorem accessReads_bounds_iff (addressDependency : accessReads regions access)
    (maskDependency : maskReads regions mask) (M : Algebra α)
    (precision : Option ComputeDType) (bounds : RegionName → Nat)
    (first second : State α) (same : first.AgreesOn regions second) :
    Safety.addressSafe M precision bounds first access (Safety.maskActive M precision first mask) ↔
    Safety.addressSafe M precision bounds second access (Safety.maskActive M precision second mask) := by
  cases access with
  | ptr | blockPtr => simp [accessReads] at addressDependency
  | region region offset =>
      have addresses := Reads.eval_eq addressDependency M precision first second same
      cases mask with
      | none => simp only [Safety.addressSafe,Safety.maskActive,addresses]
      | mask condition =>
          simp only [Safety.addressSafe,Safety.maskActive,addresses,
            Reads.eval_eq maskDependency M precision first second same]
      | maskOther condition other =>
          simp only [Safety.addressSafe,Safety.maskActive,addresses,
            Reads.eval_eq maskDependency.1 M precision first second same]

theorem algDependencies_safe_iff (M : Algebra α) (regions : RegionName → Prop) (statement : Stmt)
    (dependency : algDependencies regions statement) (bounds : RegionName → Nat)
    (first second : State α) (same : first.AgreesOn regions second) :
    Safety.safeAlg M bounds statement first ↔ Safety.safeAlg M bounds statement second := by
  unfold Safety.safeAlg
  split
  · exact Reads.safe_iff dependency M none bounds first second same
  · exact and_congr (accessReads_safe_iff dependency.1 M none bounds first second same)
      (and_congr (dependency.2.2.safe_iff M none bounds first second same)
        (and_congr (maskReads_safe_iff dependency.2.1 M none bounds first second same)
          (accessReads_bounds_iff dependency.1 dependency.2.1 M none bounds first second same)))
  · exact and_congr (accessReads_safe_iff dependency.1 M none bounds first second same)
      (and_congr (dependency.2.2.safe_iff M none bounds first second same)
        (and_congr (maskReads_safe_iff dependency.2.1 M none bounds first second same)
          (accessReads_bounds_iff dependency.1 dependency.2.1 M none bounds first second same)))
  · exact and_congr Iff.rfl (and_congr (accessReads_safe_iff dependency.1 M none bounds first second same)
      (and_congr (dependency.2.2.safe_iff M none bounds first second same)
        (and_congr (maskReads_safe_iff dependency.2.1 M none bounds first second same)
          (accessReads_bounds_iff dependency.1 dependency.2.1 M none bounds first second same))))
  · rfl

theorem readDependencies_leaf_safe_iff (M : Algebra α) (regions : RegionName → Prop)
    (statement : ComputeStmt) (dependency : readDependencies regions statement)
    (supported : Interleaved.leafSupported statement = true) (bounds : RegionName → Nat)
    (first second : State α) (same : first.AgreesOn regions second) :
    Safety.stepSafe M bounds statement first ↔ Safety.stepSafe M bounds statement second := by
  cases statement with
  | alg statement =>
      simp only [Safety.stepSafe]
      simp only [readDependencies] at dependency
      exact algDependencies_safe_iff M regions statement dependency bounds first second same
  | assign dtype shape name expression =>
      simp only [Safety.stepSafe]
      simp only [readDependencies] at dependency
      exact dependency.safe_iff M bounds first second same
  | store dtype shape access expression mask | atomicAdd dtype shape access expression mask =>
      simp only [Safety.stepSafe]
      simp only [readDependencies] at dependency
      exact and_congr (accessReads_safe_iff dependency.1 M none bounds first second same)
        (and_congr (dependency.2.2.safe_iff M bounds first second same)
          (and_congr (maskReads_safe_iff dependency.2.1 M none bounds first second same)
            (accessReads_bounds_iff dependency.1 dependency.2.1 M none bounds first second same)))
  | atomicRMW operation dtype shape access expression result mask order =>
      cases result <;> cases order <;> try { simp [Interleaved.leafSupported] at supported }
      simp only [Safety.stepSafe]
      simp only [readDependencies] at dependency
      exact and_congr Iff.rfl (and_congr (accessReads_safe_iff dependency.1 M none bounds first second same)
        (and_congr (dependency.2.2.safe_iff M bounds first second same)
          (and_congr (maskReads_safe_iff dependency.2.1 M none bounds first second same)
            (accessReads_bounds_iff dependency.1 dependency.2.1 M none bounds first second same))))
  | forLoop | forRange | forRangeDyn | forRangeInt | ifThen | ifThenElse | effectMarker =>
      simp [Interleaved.leafSupported] at supported

#axiomsClean readDependencies_leaf_safe_iff
#axiomsClean accessReads_safe_iff
#axiomsClean maskReads_safe_iff
#axiomsClean accessReads_bounds_iff
#axiomsClean algDependencies_safe_iff
end
end VeriTile.Triton.FP.Structural
