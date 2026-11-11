import VeriTile.Triton.Float.LeafWriteTrace
import VeriTile.Triton.Float.SourceReadDependency

/-! Emitted primitive write operands depend on the same declared inputs as
source expressions. Atomic events retain their primitive combiner but do not
capture the old destination word; replay supplies that word in schedule order. -/
namespace VeriTile.Triton.FP.Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

theorem storeEvents_agree (M : Algebra α) (regions : RegionName → Prop)
    (region : Region dtype) (offset : Op .nat shape) (mask : MaskOpt dtype shape)
    (first second : State α) (same : first.AgreesOn regions second)
    (addresses : Reads regions offset) (masks : maskReads regions mask) (values : Values α dtype shape) :
    storeEvents M region offset mask values first = storeEvents M region offset mask values second := by
  simp only [storeEvents,addresses.eval_eq M none first second same,writeMask_eq M masks first second same]

theorem atomicEvents_agree (M : Algebra α) (kind : AtomicKind) (numeric : NumericDType dtype)
    (regions : RegionName → Prop) (region : Region dtype) (offset : Op .nat shape) (mask : MaskOpt dtype shape)
    (first second : State α) (same : first.AgreesOn regions second)
    (addresses : Reads regions offset) (masks : maskReads regions mask) (values : Values α dtype shape) :
    atomicEvents M kind numeric region offset mask values first = atomicEvents M kind numeric region offset mask values second := by
  simp only [atomicEvents,addresses.eval_eq M none first second same,writeMask_eq M masks first second same]

theorem atomicReductionEvents_agree (M : Algebra α) (operation : RMWOp)
    (regions : RegionName → Prop) (region : Region dtype) (offset : Op .nat shape) (mask : MaskOpt dtype shape)
    (first second : State α) (same : first.AgreesOn regions second)
    (addresses : Reads regions offset) (masks : maskReads regions mask) (values : Values α dtype shape) :
    atomicReductionEvents M operation region offset mask values first = atomicReductionEvents M operation region offset mask values second := by
  cases dtype <;> cases operation <;> simp [atomicReductionEvents]
  all_goals exact atomicEvents_agree _ _ _ regions _ _ _ first second same addresses masks values

theorem algWriteEvents_agree (M : Algebra α) (regions : RegionName → Prop) (statement : Stmt)
    (dependent : algDependencies regions statement) (first second : State α) (same : first.AgreesOn regions second) :
    algWriteEvents M statement first = algWriteEvents M statement second := by
  cases statement with
  | assign => rfl
  | store dtype shape access value mask =>
      cases access with
      | ptr | blockPtr => simp [algDependencies,accessReads] at dependent
      | region region offset =>
          simp only [algDependencies,accessReads] at dependent
          have values := dependent.2.2.eval_eq M none first second same
          simp only [algWriteEvents,values,storeEvents_agree M regions region offset mask first second same dependent.1 dependent.2.1]
  | atomicAdd numeric shape access value mask =>
      cases access with
      | ptr | blockPtr => simp [algDependencies,accessReads] at dependent
      | region region offset =>
          simp only [algDependencies,accessReads] at dependent
          have values := dependent.2.2.eval_eq M none first second same
          simp only [algWriteEvents,values,atomicEvents_agree M .add numeric regions region offset mask first second same dependent.1 dependent.2.1]
  | atomicRMW operation dtype shape access value extra mask result =>
      cases extra with
      | some extra => simp [algDependencies] at dependent
      | none =>
        cases result with
        | some result => simp [algDependencies] at dependent
        | none =>
          cases access with
          | ptr | blockPtr => simp [algDependencies,accessReads] at dependent
          | region region offset =>
              simp only [algDependencies,accessReads] at dependent
              have values := dependent.2.2.eval_eq M none first second same
              simp only [algWriteEvents,values,atomicReductionEvents_agree M operation regions region offset mask first second same dependent.1 dependent.2.1]
  | forLoop | forRange | forRangeDyn | forRangeInt | ifThen | ifThenElse => simp [algDependencies] at dependent

theorem leafWriteEvents_agree (M : Algebra α) (regions : RegionName → Prop) (statement : ComputeStmt)
    (dependent : readDependencies regions statement) (first second : State α) (same : first.AgreesOn regions second) :
    leafWriteEvents M statement first = leafWriteEvents M statement second := by
  cases statement with
  | alg statement =>
      exact algWriteEvents_agree M regions statement (by simpa only [readDependencies] using dependent) first second same
  | assign => rfl
  | store dtype shape access value mask =>
      cases access with
      | ptr | blockPtr => simp [readDependencies,accessReads] at dependent
      | region region offset =>
          simp only [readDependencies,accessReads] at dependent
          have values := dependent.2.2.eval_eq M first second same
          simp only [leafWriteEvents,values,storeEvents_agree M regions region offset mask first second same dependent.1 dependent.2.1]
  | atomicAdd numeric shape access value mask =>
      cases access with
      | ptr | blockPtr => simp [readDependencies,accessReads] at dependent
      | region region offset =>
          simp only [readDependencies,accessReads] at dependent
          have values := dependent.2.2.eval_eq M first second same
          simp only [leafWriteEvents,values,atomicEvents_agree M .add numeric regions region offset mask first second same dependent.1 dependent.2.1]
  | atomicRMW operation dtype shape access value extra mask result =>
      cases extra with
      | some extra => simp [readDependencies] at dependent
      | none =>
        cases result with
        | some result => simp [readDependencies] at dependent
        | none =>
          cases access with
          | ptr | blockPtr => simp [readDependencies,accessReads] at dependent
          | region region offset =>
              simp only [readDependencies,accessReads] at dependent
              have values := dependent.2.2.eval_eq M first second same
              simp only [leafWriteEvents,values,atomicReductionEvents_agree M operation regions region offset mask first second same dependent.1 dependent.2.1]
  | forLoop | forRange | forRangeDyn | forRangeInt | ifThen | ifThenElse | effectMarker => rfl

#axiomsClean storeEvents_agree
#axiomsClean atomicEvents_agree
#axiomsClean atomicReductionEvents_agree
#axiomsClean algWriteEvents_agree
#axiomsClean leafWriteEvents_agree
end
end VeriTile.Triton.FP.Structural
