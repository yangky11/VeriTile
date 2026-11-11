import VeriTile.Triton.Float.ComputeReadDependency
import VeriTile.Triton.Float.SourceReadOnly

/-! Named-region address and mask dependencies determine whether the actual
store/atomic interpreter succeeds. Destination contents may differ: discarded
atomic results do not change local registers or protected input regions. -/
namespace VeriTile.Triton.FP.Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

def accessReads (regions : RegionName → Prop) : MemAccess dtype shape → Prop
  | .region _ offset => Reads regions offset
  | _ => False

def maskReads (regions : RegionName → Prop) : MaskOpt dtype shape → Prop
  | .none => True
  | .mask expression => Reads regions expression
  | .maskOther expression other => Reads regions expression ∧ Reads regions other

variable {α : Type} [Inhabited α]

theorem store_present_eq (M : Algebra α) {dtype : TileDType} {shape : TileShape}
    (regions : RegionName → Prop) (access : MemAccess dtype shape) (mask : MaskOpt dtype shape)
    (addressDependency : accessReads regions access) (maskDependency : maskReads regions mask)
    (values : Values α dtype shape) (first second : State α) (same : first.AgreesOn regions second) :
    (store M access mask values first).isSome = (store M access mask values second).isSome := by
  cases access with
  | ptr | blockPtr => simp [accessReads] at addressDependency
  | region region offset =>
      have addresses := Reads.eval_eq addressDependency M none first second same
      cases mask with
      | none =>
          unfold store
          dsimp only
          rw [addresses]
          cases evalOp M none offset second <;> rfl
      | mask condition =>
          have masks := Reads.eval_eq maskDependency M none first second same
          unfold store
          dsimp only
          rw [addresses,masks]
          cases evalOp M none offset second <;> cases evalOp M none condition second <;> rfl
      | maskOther condition other =>
          have masks := Reads.eval_eq maskDependency.1 M none first second same
          unfold store
          dsimp only
          rw [addresses,masks]
          cases evalOp M none offset second <;> cases evalOp M none condition second <;> rfl

theorem atomicAdd_present_eq (M : Algebra α) {dtype : TileDType} {shape : TileShape}
    (regions : RegionName → Prop) (numeric : NumericDType dtype) (access : MemAccess dtype shape) (mask : MaskOpt dtype shape)
    (addressDependency : accessReads regions access) (maskDependency : maskReads regions mask)
    (values : Values α dtype shape) (first second : State α) (same : first.AgreesOn regions second) :
    (atomicAdd M numeric access mask values first).isSome = (atomicAdd M numeric access mask values second).isSome := by
  cases access with
  | ptr | blockPtr => simp [accessReads] at addressDependency
  | region region offset =>
      have addresses := Reads.eval_eq addressDependency M none first second same
      cases mask with
      | none =>
          unfold atomicAdd
          dsimp only
          rw [addresses]
          cases atomicAddition M numeric <;> cases evalOp M none offset second <;> rfl
      | mask condition =>
          have masks := Reads.eval_eq maskDependency M none first second same
          unfold atomicAdd
          dsimp only
          rw [addresses,masks]
          cases atomicAddition M numeric <;> cases evalOp M none offset second <;> cases evalOp M none condition second <;> rfl
      | maskOther condition other =>
          have masks := Reads.eval_eq maskDependency.1 M none first second same
          unfold atomicAdd
          dsimp only
          rw [addresses,masks]
          cases atomicAddition M numeric <;> cases evalOp M none offset second <;> cases evalOp M none condition second <;> rfl

theorem atomicReduction_present_eq (M : Algebra α) (operation : RMWOp) {dtype : TileDType} {shape : TileShape}
    (regions : RegionName → Prop) (access : MemAccess dtype shape) (mask : MaskOpt dtype shape)
    (addressDependency : accessReads regions access) (maskDependency : maskReads regions mask)
    (values : Values α dtype shape) (first second : State α) (same : first.AgreesOn regions second) :
    (atomicReduction M operation access mask values first).isSome =
      (atomicReduction M operation access mask values second).isSome := by
  unfold atomicReduction
  split
  · cases dtype <;> first | rfl | exact atomicAdd_present_eq _ regions _ access mask addressDependency maskDependency values first second same
  · rfl

theorem store_agrees (M : Algebra α) {dtype : TileDType} {shape : TileShape}
    (regions : RegionName → Prop) (access : MemAccess dtype shape) (mask : MaskOpt dtype shape)
    (addressDependency : accessReads regions access) (maskDependency : maskReads regions mask)
    (outside : accessOutside regions access) (values : Values α dtype shape)
    (first second final : State α) (same : first.AgreesOn regions second)
    (ran : store M access mask values first = some final) :
    ∃ other, store M access mask values second = some other ∧ final.AgreesOn regions other := by
  have present := store_present_eq M regions access mask addressDependency maskDependency values first second same
  cases secondRun : store M access mask values second with
  | none => simp [ran,secondRun] at present
  | some other => exact ⟨other,rfl,
      ((store_access_frame M regions access outside mask values first final ran).trans same).trans
        (store_access_frame M regions access outside mask values second other secondRun).symm⟩

theorem atomicAdd_agrees (M : Algebra α) {dtype : TileDType} {shape : TileShape}
    (regions : RegionName → Prop) (numeric : NumericDType dtype) (access : MemAccess dtype shape) (mask : MaskOpt dtype shape)
    (addressDependency : accessReads regions access) (maskDependency : maskReads regions mask)
    (outside : accessOutside regions access) (values : Values α dtype shape)
    (first second final : State α) (same : first.AgreesOn regions second)
    (ran : atomicAdd M numeric access mask values first = some final) :
    ∃ other, atomicAdd M numeric access mask values second = some other ∧ final.AgreesOn regions other := by
  have present := atomicAdd_present_eq M regions numeric access mask addressDependency maskDependency values first second same
  cases secondRun : atomicAdd M numeric access mask values second with
  | none => simp [ran,secondRun] at present
  | some other => exact ⟨other,rfl,
      ((atomicAdd_access_frame M regions numeric access outside mask values first final ran).trans same).trans
        (atomicAdd_access_frame M regions numeric access outside mask values second other secondRun).symm⟩

theorem atomicReduction_agrees (M : Algebra α) (operation : RMWOp) {dtype : TileDType} {shape : TileShape}
    (regions : RegionName → Prop) (access : MemAccess dtype shape) (mask : MaskOpt dtype shape)
    (addressDependency : accessReads regions access) (maskDependency : maskReads regions mask)
    (outside : accessOutside regions access) (values : Values α dtype shape)
    (first second final : State α) (same : first.AgreesOn regions second)
    (ran : atomicReduction M operation access mask values first = some final) :
    ∃ other, atomicReduction M operation access mask values second = some other ∧ final.AgreesOn regions other := by
  have present := atomicReduction_present_eq M operation regions access mask addressDependency maskDependency values first second same
  cases secondRun : atomicReduction M operation access mask values second with
  | none => simp [ran,secondRun] at present
  | some other => exact ⟨other,rfl,
      ((atomicReduction_access_frame M operation regions access outside mask values first final ran).trans same).trans
        (atomicReduction_access_frame M operation regions access outside mask values second other secondRun).symm⟩

#axiomsClean store_present_eq
#axiomsClean atomicAdd_present_eq
#axiomsClean atomicReduction_present_eq
#axiomsClean store_agrees
#axiomsClean atomicAdd_agrees
#axiomsClean atomicReduction_agrees
end
end VeriTile.Triton.FP.Structural
