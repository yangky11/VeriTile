import VeriTile.Triton.Float.ComputeReadDependency
import VeriTile.Triton.Float.StructuralSafety

/-! Access safety follows the same structural read dependencies as execution.
It is invariant under changes outside declared input regions. -/
namespace VeriTile.Triton.FP.Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

theorem Reads.safe_iff (reads : Reads regions expression) (M : Algebra α)
    (precision : Option ComputeDType) (bounds : RegionName → Nat)
    (first second : State α) (same : first.AgreesOn regions second) :
    Safety.safeOp M precision bounds first expression ↔ Safety.safeOp M precision bounds second expression := by
  induction reads generalizing precision first second with
  | const  => simp only [Safety.safeOp]
  | constFloat  => simp only [Safety.safeOp]
  | constNat  => simp only [Safety.safeOp]
  | constInt  => simp only [Safety.safeOp]
  | constBool  => simp only [Safety.safeOp]
  | negInf  => simp only [Safety.safeOp]
  | arange  => simp only [Safety.safeOp]
  | programId axis => simp only [Safety.safeOp]
  | numPrograms axis => simp only [Safety.safeOp]
  | ref dtype shape name => simp only [Safety.safeOp]
  | «broadcast» output _ ih =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      rw [ih precision first second same]
  | «full» output _ ih =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      rw [ih precision first second same]
  | «withPrecision» dtype policy _ ih =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      rw [ih _ first second same]
  | «castFloat» src dst _ ih =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      rw [ih precision first second same]
  | «castNatToInt» _ ih =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      rw [ih precision first second same]
  | «castIntToNat» _ ih =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      rw [ih precision first second same]
  | «sqrt» _ ih =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      rw [ih precision first second same]
  | «transpose» _ ih =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      rw [ih precision first second same]
  | «absFloat» dtype _ ih =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      rw [ih precision first second same]
  | «reduceMax» axis keep _ ih =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      rw [ih precision first second same]
  | «reshape» output _ ih =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      rw [ih precision first second same]
  | «split» side _ ih =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      rw [ih precision first second same]
  | «expandDim» axis _ ih =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      rw [ih precision first second same]
  | «remap» output index _ ih =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      rw [ih precision first second same]
  | add numeric bc _ _ ihLeft ihRight =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      rw [ihLeft precision first second same,ihRight precision first second same]
  | sub numeric bc _ _ ihLeft ihRight =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      rw [ihLeft precision first second same,ihRight precision first second same]
  | mul numeric bc _ _ ihLeft ihRight =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      rw [ihLeft precision first second same,ihRight precision first second same]
  | div numeric bc _ _ ihLeft ihRight =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      rw [ihLeft precision first second same,ihRight precision first second same]
  | floorDiv numeric bc _ _ ihLeft ihRight =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      rw [ihLeft precision first second same,ihRight precision first second same]
  | mod numeric bc _ _ ihLeft ihRight =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      rw [ihLeft precision first second same,ihRight precision first second same]
  | lt numeric bc _ _ ihLeft ihRight =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      rw [ihLeft precision first second same,ihRight precision first second same]
  | maximumFloat numeric bc _ _ ihLeft ihRight =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      rw [ihLeft precision first second same,ihRight precision first second same]
  | minimumFloat numeric bc _ _ ihLeft ihRight =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      rw [ihLeft precision first second same,ihRight precision first second same]
  | boolAnd bc _ _ ihLeft ihRight =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      rw [ihLeft precision first second same,ihRight precision first second same]
  | «where» _ _ _ ihCondition ihYes ihNo =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      rw [ihCondition precision first second same,ihYes precision first second same,ihNo precision first second same]
  | «dotAcc» leftType rightType outType options _ _ _ ihLeft ihRight ihAcc =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      rw [ihLeft precision first second same,ihRight precision first second same,ihAcc precision first second same]
  | @loadNone dtype shape region offset padding member offsetRead ihOffset =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      dsimp only
      rw [ihOffset precision first second same]
      simp only [Safety.addressSafe,Safety.maskActive,offsetRead.eval_eq M precision first second same]
  | @loadMask dtype shape region offset mask padding member offsetRead maskRead ihOffset ihMask =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      dsimp only
      rw [ihOffset precision first second same,ihMask precision first second same]
      simp only [Safety.addressSafe,Safety.maskActive,offsetRead.eval_eq M precision first second same,maskRead.eval_eq M precision first second same]
  | @loadOther dtype shape region offset mask other padding member offsetRead maskRead otherRead ihOffset ihMask ihOther =>
      conv_lhs => unfold Safety.safeOp
      conv_rhs => unfold Safety.safeOp
      dsimp only
      rw [ihOffset precision first second same,ihMask precision first second same,ihOther precision first second same]
      simp only [Safety.addressSafe,Safety.maskActive,offsetRead.eval_eq M precision first second same,maskRead.eval_eq M precision first second same]

theorem ComputeReads.safe_iff (reads : ComputeReads regions expression) (M : Algebra α)
    (bounds : RegionName → Nat) (first second : State α) (same : first.AgreesOn regions second) :
    Safety.safeCompute M bounds first expression ↔ Safety.safeCompute M bounds second expression := by
  induction reads with
  | alg dtype dependency => exact dependency.safe_iff M (some dtype) bounds first second same
  | @const constantType value => cases constantType <;> rfl
  | «full» shape _ ih => exact ih

theorem ExprReads.safe_iff (reads : ExprReads regions expression) (M : Algebra α)
    (bounds : RegionName → Nat) (first second : State α) (same : first.AgreesOn regions second) :
    Safety.safeExpr M bounds first expression ↔ Safety.safeExpr M bounds second expression := by
  cases reads with
  | alg dependency => exact dependency.safe_iff M none bounds first second same
  | compute dependency => exact dependency.safe_iff M bounds first second same

#axiomsClean ComputeReads.safe_iff
#axiomsClean ExprReads.safe_iff
#axiomsClean Reads.safe_iff
end
end VeriTile.Triton.FP.Structural
