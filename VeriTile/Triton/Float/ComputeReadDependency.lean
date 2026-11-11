import VeriTile.Triton.Float.ReadDependency

/-! Read dependencies retain compute annotations and the actual expression
interpreter. Unsupported source effects are not introduced by a callback. -/
namespace VeriTile.Triton.FP.Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false

inductive ComputeReads (regions : RegionName → Prop) :
    {dtype : ComputeDType} → {shape : TileShape} → ComputeOp dtype shape → Prop where
  | alg (dtype : ComputeDType) {expression : Op dtype.eraseDType shape} :
      Reads regions expression → ComputeReads regions (.alg dtype expression)
  | const (value : ComputeCarrier dtype) : ComputeReads regions (.const value)
  | full (shape : TileShape) {expression : ComputeOp dtype []} :
      ComputeReads regions expression → ComputeReads regions (.full shape expression)

inductive ExprReads (regions : RegionName → Prop) :
    {dtype : TileDType} → {shape : TileShape} → ComputeExpr dtype shape → Prop where
  | alg {expression : Op dtype shape} : Reads regions expression → ExprReads regions (.alg expression)
  | compute {expression : ComputeOp dtype shape} : ComputeReads regions expression → ExprReads regions (.compute expression)

theorem ComputeReads.eval_eq {α : Type} [Inhabited α] {regions : RegionName → Prop}
    {dtype : ComputeDType} {shape : TileShape} {expression : ComputeOp dtype shape} (reads : ComputeReads regions expression)
    (M : Algebra α) (first second : State α) (same : first.AgreesOn regions second) :
    evalComputeOp M expression first = evalComputeOp M expression second := by
  induction reads with
  | alg dtype dependency => exact dependency.eval_eq M (some dtype) first second same
  | @const constantType value => cases constantType <;> rfl
  | «full» shape _ ih => simp only [evalComputeOp_full,ih]


theorem ExprReads.eval_eq {α : Type} [Inhabited α] {regions : RegionName → Prop}
    {dtype : TileDType} {shape : TileShape} {expression : ComputeExpr dtype shape} (reads : ExprReads regions expression)
    (M : Algebra α) (first second : State α) (same : first.AgreesOn regions second) :
    evalExpr M expression first = evalExpr M expression second := by
  cases reads with
  | alg dependency => exact dependency.eval_eq M none first second same
  | compute dependency => exact dependency.eval_eq M first second same

#axiomsClean ComputeReads.eval_eq
#axiomsClean ExprReads.eval_eq
end
end VeriTile.Triton.FP.Structural
