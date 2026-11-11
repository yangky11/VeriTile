import VeriTile.Triton.Float.LeafWriteTrace
import VeriTile.Triton.Float.SourceReadDependency

/-! Existing source read-dependency certificates establish that every admitted
leaf has an explicit named-region write trace; no new kernel premise is needed. -/
namespace VeriTile.Triton.FP.Structural
set_option backward.isDefEq.respectTransparency false

theorem algDependencies_writeTrace (regions : RegionName → Prop) (statement : Stmt)
    (dependent : algDependencies regions statement) : algWriteTraceSupported statement := by
  cases statement with
  | assign => trivial
  | store dtype shape access value mask | atomicAdd dtype shape access value mask =>
      cases access <;> simp_all [algDependencies,accessReads,algWriteTraceSupported]
  | atomicRMW operation dtype shape access value extra mask result =>
      cases extra <;> cases result <;> cases access <;>
        simp_all [algDependencies,accessReads,algWriteTraceSupported]
  | forLoop | forRange | forRangeDyn | forRangeInt | ifThen | ifThenElse =>
      simp [algDependencies] at dependent

theorem readDependencies_leaf_writeTrace (regions : RegionName → Prop) (statement : ComputeStmt)
    (dependent : readDependencies regions statement) (supported : Interleaved.leafSupported statement = true) :
    leafWriteTraceSupported statement := by
  cases statement with
  | alg statement => exact algDependencies_writeTrace regions statement (by simpa only [readDependencies] using dependent)
  | assign => trivial
  | store dtype shape access value mask | atomicAdd dtype shape access value mask =>
      cases access <;> simp_all [readDependencies,accessReads,leafWriteTraceSupported]
  | atomicRMW operation dtype shape access value extra mask result =>
      cases extra <;> cases result <;> cases access <;>
        simp_all [readDependencies,accessReads,leafWriteTraceSupported]
  | forLoop | forRange | forRangeDyn | forRangeInt | ifThen | ifThenElse | effectMarker =>
      simp [Interleaved.leafSupported] at supported

#axiomsClean algDependencies_writeTrace
#axiomsClean readDependencies_leaf_writeTrace
end VeriTile.Triton.FP.Structural
