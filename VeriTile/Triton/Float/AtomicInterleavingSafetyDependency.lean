import VeriTile.Triton.Float.AccessSafetyDependency
import VeriTile.Triton.Float.AtomicInterleavingDependencies

/-! Each scheduled access has the same safety conditions as its isolated
source tick when the certified input dependencies agree. -/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

theorem Local.safe_agrees (M : Algebra α) (regions : RegionName → Prop) (code : List Command)
    (dependent : pendingDependencies regions code) (bounds : RegionName → Nat)
    (first second : State α) (same : first.AgreesOn regions second) :
    (Local.mk code first).Safe M bounds first.mem ↔ (Local.mk code second).Safe M bounds second.mem := by
  cases code with
  | nil => rfl
  | cons command rest =>
    have headDependency := (pendingDependencies_cons regions command rest).mp dependent |>.1
    cases command with
    | counted | natural | integer => rfl
    | source statement =>
      cases statement with
      | forLoop | forRange => rfl
      | forRangeDyn index start stop stride body | forRangeInt index start stop stride body =>
          simp only [commandDependencies,readDependencies] at headDependency
          exact and_congr (headDependency.1.safe_iff M none bounds first second same)
            (and_congr (headDependency.2.1.safe_iff M none bounds first second same)
              (headDependency.2.2.1.safe_iff M none bounds first second same))
      | ifThen condition body | ifThenElse condition yes no =>
          simp only [commandDependencies,readDependencies] at headDependency
          exact headDependency.1.safe_iff M none bounds first second same
      | alg statement =>
          by_cases supported : leafSupported (.alg statement) = true
          · simpa only [Local.Safe,supported,true_and] using
              readDependencies_leaf_safe_iff M regions (.alg statement) headDependency supported bounds first second same
          · simp [Local.Safe,supported]
      | assign dtype shape name expression =>
          simpa only [Local.Safe,leafSupported,true_and] using
            readDependencies_leaf_safe_iff M regions (.assign dtype shape name expression) headDependency rfl bounds first second same
      | store dtype shape access expression mask =>
          simpa only [Local.Safe,leafSupported,true_and] using
            readDependencies_leaf_safe_iff M regions (.store dtype shape access expression mask) headDependency rfl bounds first second same
      | atomicAdd numeric shape access expression mask =>
          by_cases supported : leafSupported (.atomicAdd numeric shape access expression mask) = true
          · simpa only [Local.Safe,supported,true_and] using
              readDependencies_leaf_safe_iff M regions (.atomicAdd numeric shape access expression mask)
                headDependency supported bounds first second same
          · simp [Local.Safe,supported]
      | atomicRMW operation dtype shape access expression result mask order =>
          by_cases supported : leafSupported (.atomicRMW operation dtype shape access expression result mask order) = true
          · simpa only [Local.Safe,supported,true_and] using
              readDependencies_leaf_safe_iff M regions (.atomicRMW operation dtype shape access expression result mask order)
                headDependency supported bounds first second same
          · simp [Local.Safe,supported]
      | effectMarker => simp [Local.Safe,leafSupported]

#axiomsClean Local.safe_agrees
end
end VeriTile.Triton.FP.Structural.Interleaved
