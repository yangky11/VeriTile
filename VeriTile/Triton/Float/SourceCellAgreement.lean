import VeriTile.Triton.Float.CellWriteAgreement
import VeriTile.Triton.Float.SourceReadDependency

/-! Actual source leaves preserve cell agreement when their expression inputs
agree. The result applies to arbitrary ownership sets, including partial rows. -/
namespace VeriTile.Triton.FP.Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

theorem algDependencies_cells_agree (M : Algebra α) (regions : RegionName → Prop)
    (cells : RegionName → Nat → Prop) (statement : Stmt) (dependency : algDependencies regions statement)
    (first second final other : State α) (same : first.AgreesOn regions second)
    (equalCells : first.CellsAgree cells second)
    (one : stepAlg M statement first = some final) (two : stepAlg M statement second = some other) :
    final.CellsAgree cells other := by
  unfold stepAlg at one
  split at one
  · simp only [bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at one
    obtain ⟨value,read,returned⟩ := one
    have readOther := (Reads.eval_eq dependency M none first second same).symm.trans read
    simp only [stepAlg,readOther,bind,pure,Option.bind_some,Option.some.injEq] at two
    subst final other
    exact equalCells
  · obtain ⟨value,read,stored⟩ := Option.bind_eq_some_iff.mp one
    have readOther := (Reads.eval_eq dependency.2.2 M none first second same).symm.trans read
    simp only [stepAlg,readOther,bind,pure,Option.bind_some] at two
    exact store_cells_agree M regions cells _ _ dependency.1 dependency.2.1 value first second final other same equalCells stored two
  · obtain ⟨value,read,stored⟩ := Option.bind_eq_some_iff.mp one
    have readOther := (Reads.eval_eq dependency.2.2 M none first second same).symm.trans read
    simp only [stepAlg,readOther,bind,pure,Option.bind_some] at two
    exact atomicAdd_cells_agree M regions cells _ _ _ dependency.1 dependency.2.1 value first second final other same equalCells stored two
  · obtain ⟨value,read,stored⟩ := Option.bind_eq_some_iff.mp one
    have readOther := (Reads.eval_eq dependency.2.2 M none first second same).symm.trans read
    simp only [stepAlg,readOther,bind,pure,Option.bind_some] at two
    exact atomicReduction_cells_agree M _ regions cells _ _ dependency.1 dependency.2.1 value first second final other same equalCells stored two
  · contradiction

theorem readDependencies_leaf_cells_agree (M : Algebra α) (regions : RegionName → Prop)
    (cells : RegionName → Nat → Prop) (statement : ComputeStmt)
    (dependency : readDependencies regions statement) (supported : Interleaved.leafSupported statement = true)
    (first second final other : State α) (same : first.AgreesOn regions second)
    (equalCells : first.CellsAgree cells second)
    (one : step M statement first = some final) (two : step M statement second = some other) :
    final.CellsAgree cells other := by
  cases statement with
  | alg statement =>
      simp only [step] at one two
      simp only [readDependencies] at dependency
      exact algDependencies_cells_agree M regions cells statement dependency first second final other same equalCells one two
  | assign dtype shape name expression =>
      simp only [step,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at one
      simp only [readDependencies] at dependency
      obtain ⟨value,read,returned⟩ := one
      have readOther := (ExprReads.eval_eq dependency M first second same).symm.trans read
      simp only [step,readOther,bind,pure,Option.bind_some,Option.some.injEq] at two
      subst final other
      exact equalCells
  | store dtype shape access expression mask =>
      simp only [step] at one
      simp only [readDependencies] at dependency
      obtain ⟨value,read,stored⟩ := Option.bind_eq_some_iff.mp one
      have readOther := (ExprReads.eval_eq dependency.2.2 M first second same).symm.trans read
      simp only [step,readOther,bind,pure,Option.bind_some] at two
      exact store_cells_agree M regions cells access mask dependency.1 dependency.2.1 value first second final other same equalCells stored two
  | atomicAdd numeric shape access expression mask =>
      simp only [step] at one
      simp only [readDependencies] at dependency
      obtain ⟨value,read,stored⟩ := Option.bind_eq_some_iff.mp one
      have readOther := (ExprReads.eval_eq dependency.2.2 M first second same).symm.trans read
      simp only [step,readOther,bind,pure,Option.bind_some] at two
      exact atomicAdd_cells_agree M regions cells numeric access mask dependency.1 dependency.2.1 value first second final other same equalCells stored two
  | atomicRMW operation dtype shape access expression result mask order =>
      cases result <;> cases order <;> try { simp [Interleaved.leafSupported] at supported }
      simp only [step] at one
      simp only [readDependencies] at dependency
      obtain ⟨value,read,stored⟩ := Option.bind_eq_some_iff.mp one
      have readOther := (ExprReads.eval_eq dependency.2.2 M first second same).symm.trans read
      simp only [step,readOther,bind,pure,Option.bind_some] at two
      exact atomicReduction_cells_agree M operation regions cells access mask dependency.1 dependency.2.1 value first second final other same equalCells stored two
  | forLoop | forRange | forRangeDyn | forRangeInt | ifThen | ifThenElse | effectMarker =>
      simp [Interleaved.leafSupported] at supported

#axiomsClean algDependencies_cells_agree
#axiomsClean readDependencies_leaf_cells_agree
end
end VeriTile.Triton.FP.Structural
