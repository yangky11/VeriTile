import VeriTile.Triton.Float.Structural
import VeriTile.Meta.StatementAudit

/-! Compositional memory dependencies of actual source expressions. Equal
local registers and equal declared input regions suffice; all other memory may
change. The certificate is structural, with no supplied expression evaluator. -/
namespace VeriTile.Triton.FP.Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

structure State.AgreesOn {α : Type} (regions : RegionName → Prop) (first second : State α) : Prop where
  registers : first.regs = second.regs
  programs : first.pids = second.pids
  grid : first.numPids = second.numPids
  undefined : first.undef = second.undef
  memory : ∀ region, regions region → first.mem region = second.mem region

theorem State.AgreesOn.refl {α : Type} (regions : RegionName → Prop) (state : State α) :
    state.AgreesOn regions state := ⟨rfl,rfl,rfl,rfl,fun _ _ => rfl⟩

theorem State.AgreesOn.symm {α : Type} {regions : RegionName → Prop} {first second : State α}
    (same : first.AgreesOn regions second) : second.AgreesOn regions first :=
  ⟨same.registers.symm,same.programs.symm,same.grid.symm,same.undefined.symm,fun region member => (same.memory region member).symm⟩

theorem State.AgreesOn.setReg {α : Type} {regions : RegionName → Prop} {first second : State α}
    (same : first.AgreesOn regions second) (name : RegName) (dtype : TileDType) (shape : TileShape)
    (value : Values α dtype shape) :
    (first.setReg name dtype shape value).AgreesOn regions (second.setReg name dtype shape value) := by
  refine ⟨?_,same.programs,same.grid,same.undefined,same.memory⟩
  simp only [State.setReg,same.registers]

theorem State.AgreesOn.writeOutside {α : Type} {regions : RegionName → Prop} {first second : State α}
    (same : first.AgreesOn regions second) (target : RegionName) (offset : Nat) (value : Cell α)
    (outside : ¬ regions target) : (first.write target offset value).AgreesOn regions second := by
  refine ⟨same.registers,same.programs,same.grid,same.undefined,?_⟩
  intro region member
  funext address
  have different : region ≠ target := by intro equal; exact outside (equal ▸ member)
  rw [State.write_other _ _ _ _ _ _ (Or.inl different),same.memory region member]

inductive Reads (regions : RegionName → Prop) : {dtype : TileDType} → {shape : TileShape} → Op dtype shape → Prop where
  | const (value : ℝ) : Reads regions (.const value)
  | constFloat (dtype : FloatDType) (value : ℝ) : Reads regions (.constFloat dtype value)
  | constNat (value : Nat) : Reads regions (.constNat value)
  | constInt (value : Int) : Reads regions (.constInt value)
  | constBool (value : Bool) : Reads regions (.constBool value)
  | negInf : Reads regions .negInf
  | programId (axis : Nat) : Reads regions (.programId axis)
  | numPrograms (axis : Nat) : Reads regions (.numPrograms axis)
  | ref (dtype : TileDType) (shape : TileShape) (name : RegName) : Reads regions (.ref dtype shape name)
  | arange (count : Nat) : Reads regions (.arange count)
  | broadcast {input : Op dtype []} (shape : TileShape) : Reads regions input → Reads regions (.broadcast input shape)
  | full {input : Op dtype []} (shape : TileShape) : Reads regions input → Reads regions (.full shape input)
  | withPrecision (dtype : FloatDType) (precision : IndexComputePrecision) {input : Op dtype.toTileDType shape} :
      Reads regions input → Reads regions (.withPrecision dtype precision input)
  | castFloat (src dst : FloatDType) {input : Op src.toTileDType shape} :
      Reads regions input → Reads regions (.castFloat src dst input)
  | castNatToInt {input : Op .nat shape} : Reads regions input → Reads regions (.castNatToInt input)
  | castIntToNat {input : Op .int shape} : Reads regions input → Reads regions (.castIntToNat input)
  | absFloat (dtype : FloatDType) {input : Op dtype.toTileDType shape} : Reads regions input → Reads regions (.absFloat dtype input)
  | sqrt {input : Op .real shape} : Reads regions input → Reads regions (.sqrt input)
  | add (numeric : NumericDType dtype) (bc : Broadcast a b out) {left : Op dtype a} {right : Op dtype b} :
      Reads regions left → Reads regions right → Reads regions (.add numeric bc left right)
  | sub (numeric : NumericDType dtype) (bc : Broadcast a b out) {left : Op dtype a} {right : Op dtype b} :
      Reads regions left → Reads regions right → Reads regions (.sub numeric bc left right)
  | mul (numeric : NumericDType dtype) (bc : Broadcast a b out) {left : Op dtype a} {right : Op dtype b} :
      Reads regions left → Reads regions right → Reads regions (.mul numeric bc left right)
  | div (numeric : NumericDType dtype) (bc : Broadcast a b out) {left : Op dtype a} {right : Op dtype b} :
      Reads regions left → Reads regions right → Reads regions (.div numeric bc left right)
  | floorDiv (numeric : IntegralDType dtype) (bc : Broadcast a b out) {left : Op dtype a} {right : Op dtype b} :
      Reads regions left → Reads regions right → Reads regions (.floorDiv numeric bc left right)
  | mod (numeric : IntegralDType dtype) (bc : Broadcast a b out) {left : Op dtype a} {right : Op dtype b} :
      Reads regions left → Reads regions right → Reads regions (.mod numeric bc left right)
  | lt (numeric : ComparableDType dtype) (bc : Broadcast a b out) {left : Op dtype a} {right : Op dtype b} :
      Reads regions left → Reads regions right → Reads regions (.lt numeric bc left right)
  | boolAnd (bc : Broadcast a b out) {left : Op .bool a} {right : Op .bool b} :
      Reads regions left → Reads regions right → Reads regions (.boolAnd bc left right)
  | maximumFloat (dtype : FloatDType) (bc : Broadcast a b out) {left : Op dtype.toTileDType a} {right : Op dtype.toTileDType b} :
      Reads regions left → Reads regions right → Reads regions (.maximumFloat dtype bc left right)
  | minimumFloat (dtype : FloatDType) (bc : Broadcast a b out) {left : Op dtype.toTileDType a} {right : Op dtype.toTileDType b} :
      Reads regions left → Reads regions right → Reads regions (.minimumFloat dtype bc left right)
  | where {condition : Op .bool shape} {yes no : Op dtype shape} :
      Reads regions condition → Reads regions yes → Reads regions no → Reads regions (.where condition yes no)
  | reduceMax (axis : Fin shape.length) (keep : Bool) {input : Op .real shape} :
      Reads regions input → Reads regions (.reduceMax axis keep input)
  | transpose {input : Op dtype (batch ++ [m,n])} : Reads regions input → Reads regions (.transpose input)
  | reshape (output : TileShape) {input : Op dtype shape} : Reads regions input → Reads regions (.reshape output input)
  | remap (output : TileShape) (index : TileIndex output → TileIndex shape) {input : Op dtype shape} :
      Reads regions input → Reads regions (.remap output index input)
  | split (side : Fin 2) {input : Op dtype (shape ++ [2])} : Reads regions input → Reads regions (.split side input)
  | expandDim (axis : Fin (shape.length+1)) {input : Op dtype shape} : Reads regions input → Reads regions (.expandDim axis input)
  | dotAcc (leftType rightType outType : FloatDType) (options : DotOptions)
      {left : Op leftType.toTileDType (batch ++ [m,k])} {right : Op rightType.toTileDType (batch ++ [k,n])}
      {acc : Op outType.toTileDType (batch ++ [m,n])} : Reads regions left → Reads regions right → Reads regions acc →
      Reads regions (.dotAcc leftType rightType outType left right acc options)
  | loadNone (region : Region dtype) {offset : Op .nat shape} (padding : PaddingOption) :
      regions (Region.cast region) → Reads regions offset → Reads regions (.load dtype (.region region offset) .none padding)
  | loadMask (region : Region dtype) {offset : Op .nat shape} {mask : Op .bool shape} (padding : PaddingOption) :
      regions (Region.cast region) → Reads regions offset → Reads regions mask →
      Reads regions (.load dtype (.region region offset) (.mask mask) padding)
  | loadOther (region : Region dtype) {offset : Op .nat shape} {mask : Op .bool shape} {other : Op dtype shape} (padding : PaddingOption) :
      regions (Region.cast region) → Reads regions offset → Reads regions mask → Reads regions other →
      Reads regions (.load dtype (.region region offset) (.maskOther mask other) padding)

theorem Reads.eval_eq {α : Type} [Inhabited α] {regions : RegionName → Prop}
    {dtype : TileDType} {shape : TileShape} {expression : Op dtype shape} (reads : Reads regions expression)
    (M : Algebra α) (precision : Option ComputeDType) (first second : State α) (same : first.AgreesOn regions second) :
    evalOp M precision expression first = evalOp M precision expression second := by
  induction reads generalizing precision first second with
  | const  => rfl
  | constFloat  => rfl
  | constNat  => rfl
  | constInt  => rfl
  | constBool  => rfl
  | negInf  => rfl
  | arange  => rfl
  | programId axis => simp only [evalOp_unfold,same.programs]
  | numPrograms axis => simp only [evalOp_unfold,same.grid]
  | ref dtype shape name => simp only [evalOp_unfold,same.registers]
  | «broadcast» output _ ih =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      rw [ih precision first second same]
  | «full» output _ ih =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      rw [ih precision first second same]
  | «withPrecision» dtype policy _ ih =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      rw [ih _ first second same]
  | «castFloat» src dst _ ih =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      rw [ih precision first second same]
  | «castNatToInt» _ ih =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      rw [ih precision first second same]
  | «castIntToNat» _ ih =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      rw [ih precision first second same]
  | «sqrt» _ ih =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      rw [ih precision first second same]
  | «transpose» _ ih =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      rw [ih precision first second same]
  | «absFloat» dtype _ ih =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      rw [ih precision first second same]
  | «reduceMax» axis keep _ ih =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      rw [ih precision first second same]
  | «reshape» output _ ih =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      rw [ih precision first second same]
  | «split» side _ ih =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      rw [ih precision first second same]
  | «expandDim» axis _ ih =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      rw [ih precision first second same]
  | «remap» output index _ ih =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      rw [ih precision first second same]
  | add numeric bc _ _ ihLeft ihRight =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      rw [ihLeft precision first second same,ihRight precision first second same]
  | sub numeric bc _ _ ihLeft ihRight =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      rw [ihLeft precision first second same,ihRight precision first second same]
  | mul numeric bc _ _ ihLeft ihRight =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      rw [ihLeft precision first second same,ihRight precision first second same]
  | div numeric bc _ _ ihLeft ihRight =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      rw [ihLeft precision first second same,ihRight precision first second same]
  | floorDiv numeric bc _ _ ihLeft ihRight =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      rw [ihLeft precision first second same,ihRight precision first second same]
  | mod numeric bc _ _ ihLeft ihRight =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      rw [ihLeft precision first second same,ihRight precision first second same]
  | lt numeric bc _ _ ihLeft ihRight =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      rw [ihLeft precision first second same,ihRight precision first second same]
  | maximumFloat numeric bc _ _ ihLeft ihRight =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      rw [ihLeft precision first second same,ihRight precision first second same]
  | minimumFloat numeric bc _ _ ihLeft ihRight =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      rw [ihLeft precision first second same,ihRight precision first second same]
  | boolAnd bc _ _ ihLeft ihRight =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      rw [ihLeft precision first second same,ihRight precision first second same]
  | «where» _ _ _ ihCondition ihYes ihNo =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      rw [ihCondition precision first second same,ihYes precision first second same,ihNo precision first second same]
  | «dotAcc» leftType rightType outType options _ _ _ ihLeft ihRight ihAcc =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      rw [ihLeft precision first second same,ihRight precision first second same,ihAcc precision first second same]
  | @loadNone dtype shape region offset padding member _ ihOffset =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      dsimp only
      rw [ihOffset precision first second same]
      cases evalOp M precision offset second
      all_goals simp [same.undefined,same.memory (Region.cast region) member]
  | @loadMask dtype shape region offset mask padding member _ _ ihOffset ihMask =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      dsimp only
      rw [ihOffset precision first second same,ihMask precision first second same]
      cases evalOp M precision offset second <;> cases evalOp M precision mask second
      all_goals simp [same.undefined,same.memory (Region.cast region) member]
  | @loadOther dtype shape region offset mask other padding member _ _ _ ihOffset ihMask ihOther =>
      conv_lhs => unfold evalOp
      conv_rhs => unfold evalOp
      dsimp only
      rw [ihOffset precision first second same,ihMask precision first second same,ihOther precision first second same]
      cases evalOp M precision offset second <;> cases evalOp M precision mask second <;> cases evalOp M precision other second
      all_goals simp [same.memory (Region.cast region) member]

#axiomsClean State.AgreesOn.refl
#axiomsClean State.AgreesOn.symm
#axiomsClean State.AgreesOn.setReg
#axiomsClean State.AgreesOn.writeOutside
#axiomsClean Reads.eval_eq
end
end VeriTile.Triton.FP.Structural
