import VeriTile.Triton.Float.CellAgreement
import VeriTile.Triton.Float.AccessSafetyDependency

/-! Named-region writes expose their actual evaluated masks and offsets. These
lemmas retain the evaluator's lane order and state-dependent atomic words. -/
namespace VeriTile.Triton.FP.Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

def writeMask (M : Algebra α) (mask : MaskOpt dtype shape) (state : State α) : Option (TileIndex shape → Bool) :=
  match mask with
  | .none => some (fun _ => true)
  | .mask condition | .maskOther condition _ => evalOp M none condition state

theorem writeMask_eq (M : Algebra α) (dependency : maskReads regions mask)
    (first second : State α) (same : first.AgreesOn regions second) :
    writeMask M mask first = writeMask M mask second := by
  cases mask with
  | none => rfl
  | mask condition => exact Reads.eval_eq dependency M none first second same
  | maskOther condition other => exact dependency.1.eval_eq M none first second same

theorem writeMask_active (M : Algebra α) (mask : MaskOpt dtype shape) (state : State α)
    (active : TileIndex shape → Bool) (read : writeMask M mask state = some active)
    (lane : TileIndex shape) (selected : active lane = true) : Safety.maskActive M none state mask lane := by
  cases mask with
  | none => trivial
  | mask condition | maskOther condition other => exact ⟨active,read,selected⟩

theorem store_region_eq (M : Algebra α) (region : Region dtype) (offset : Op .nat shape)
    (mask : MaskOpt dtype shape) (values : Values α dtype shape) (state : State α) :
    store M (.region region offset) mask values state =
      (evalOp M none offset state).bind (fun offsets => (writeMask M mask state).bind (fun active => some (
        (TileShape.allIndices shape).foldl (fun current lane =>
          if active lane then current.write (Region.cast region) (offsets lane) (.mk dtype (values lane)) else current) state))) := by
  cases addresses : evalOp M none offset state <;> cases mask <;> simp [store,writeMask,addresses]

theorem atomicAdd_region_eq (M : Algebra α) (numeric : NumericDType dtype)
    (region : Region dtype) (offset : Op .nat shape) (mask : MaskOpt dtype shape)
    (values : Values α dtype shape) (state : State α) :
    atomicAdd M numeric (.region region offset) mask values state =
      (atomicAddition M numeric).bind (fun combine =>
        (evalOp M none offset state).bind (fun offsets => (writeMask M mask state).bind (fun active => some (
          (TileShape.allIndices shape).foldl (fun current lane =>
            if active lane then current.write (Region.cast region) (offsets lane)
              (.mk dtype (combine ((current.mem (Region.cast region) (offsets lane)).read dtype) (values lane)))
            else current) state)))) := by
  cases available : atomicAddition M numeric <;> cases addresses : evalOp M none offset state <;>
    cases mask <;> simp [atomicAdd,writeMask,available,addresses]

#axiomsClean writeMask_eq
#axiomsClean writeMask_active
#axiomsClean store_region_eq
#axiomsClean atomicAdd_region_eq
end
end VeriTile.Triton.FP.Structural
