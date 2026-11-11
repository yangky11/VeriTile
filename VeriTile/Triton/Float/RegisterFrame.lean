import VeriTile.Triton.Float.Structural
import VeriTile.Meta.StatementAudit

/-! A register frame check for assignment/store/branch sequences. It supports
arbitrary expressions and storage accesses, but does not assert their success
or any numerical identity. Outer loops can compose it with `loop_invariant`.
Unsupported effects and nested loops fail the check. -/
namespace VeriTile.Triton.FP.Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

mutual
  def registerUntouched (name : RegName) : ComputeStmt → Bool
    | .assign _ _ target _ => decide (name ≠ target)
    | .store .. => Bool.true
    | .ifThen _ body => registersUntouched name body
    | .ifThenElse _ yes no => registersUntouched name yes && registersUntouched name no
    | _ => Bool.false
  termination_by statement => sizeOf statement
  decreasing_by all_goals (simp_wf; try omega)

  def registersUntouched (name : RegName) : List ComputeStmt → Bool
    | [] => Bool.true
    | statement :: rest => registerUntouched name statement && registersUntouched name rest
  termination_by body => sizeOf body
  decreasing_by all_goals (simp_wf; try omega)
end

theorem fold_write_registers {α ι : Type} (addresses : ι → RegionName × Nat)
    (values : ι → Cell α) (active : ι → Bool) (indices : List ι) (initial : State α) :
    (indices.foldl (fun state i => if active i then
      state.write (addresses i).1 (addresses i).2 (values i) else state) initial).regs = initial.regs := by
  induction indices generalizing initial with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    split <;> rfl

theorem store_registers {α : Type} [Inhabited α] (M : Algebra α)
    {dtype : TileDType} {shape : TileShape} (access : MemAccess dtype shape)
    (mask : MaskOpt dtype shape) (values : Values α dtype shape)
    (initial final : State α) (ran : store M access mask values initial = some final) :
    final.regs = initial.regs := by
  cases access <;>
    simp only [store,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at ran
  case region | ptr =>
    obtain ⟨addresses,_,active,_,rfl⟩ := ran
    apply fold_write_registers
  case blockPtr axes ptr =>
    obtain ⟨addresses,_,active,_,rfl⟩ := ran
    exact fold_write_registers
      (fun i => ((addresses i).region,(addresses i).address (TileShape.indexToList shape i)))
      (fun i => Cell.mk dtype (values i))
      (fun i => active i && (addresses i).inBounds (TileShape.indexToList shape i) axes)
      _ initial

variable {α : Type} [Inhabited α]
mutual
  theorem step_register_frame (M : Algebra α) (name : RegName) (statement : ComputeStmt)
      (checked : registerUntouched name statement = Bool.true) (initial final : State α)
      (ran : step M statement initial = some final) (dtype : TileDType) (shape : TileShape) :
      final.regs dtype shape name = initial.regs dtype shape name := by
    cases statementCase : statement with
    | assign d sh target expression =>
      rw [statementCase] at checked ran
      have different : name ≠ target := by simpa [registerUntouched] using checked
      simp only [step,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at ran
      obtain ⟨value,_,rfl⟩ := ran
      exact State.setReg_ne_name initial target name d dtype sh shape value different
    | store d sh access expression mask =>
      rw [statementCase] at checked ran
      simp only [step,bind,Option.bind_eq_some_iff] at ran
      obtain ⟨value,_,stored⟩ := ran
      rw [store_registers M access mask value initial final stored]
    | ifThen condition body =>
      rw [statementCase] at checked ran
      simp only [registerUntouched] at checked
      simp only [step,bind,Option.bind_eq_some_iff] at ran
      obtain ⟨conditionValue,_,branch⟩ := ran
      split at branch
      · exact run_register_frame M name body checked initial final branch dtype shape
      · cases Option.some.inj branch
        rfl
    | ifThenElse condition yes no =>
      rw [statementCase] at checked ran
      simp only [registerUntouched,Bool.and_eq_true] at checked
      have both := checked
      simp only [step,bind,Option.bind_eq_some_iff] at ran
      obtain ⟨conditionValue,_,branch⟩ := ran
      split at branch
      · exact run_register_frame M name yes both.1 initial final branch dtype shape
      · exact run_register_frame M name no both.2 initial final branch dtype shape
    | alg | atomicAdd | atomicRMW | forLoop | forRange | forRangeDyn | forRangeInt | effectMarker =>
      rw [statementCase] at checked ran
      simp [registerUntouched] at checked
  termination_by sizeOf statement
  decreasing_by all_goals (simp_all; try omega)

  theorem run_register_frame (M : Algebra α) (name : RegName) (body : List ComputeStmt)
      (checked : registersUntouched name body = Bool.true) (initial final : State α)
      (ran : run M body initial = some final) (dtype : TileDType) (shape : TileShape) :
      final.regs dtype shape name = initial.regs dtype shape name := by
    cases bodyCase : body with
    | nil =>
      rw [bodyCase] at checked ran
      simp only [run,Option.some.injEq] at ran
      cases ran
      rfl
    | cons statement rest =>
      rw [bodyCase] at checked ran
      simp only [registersUntouched,Bool.and_eq_true] at checked
      have both := checked
      simp only [run,bind,Option.bind_eq_some_iff] at ran
      obtain ⟨middle,first,last⟩ := ran
      exact (run_register_frame M name rest both.2 middle final last dtype shape).trans
        (step_register_frame M name statement both.1 initial middle first dtype shape)
  termination_by sizeOf body
  decreasing_by all_goals (simp_all; try omega)
end

#axiomsClean fold_write_registers
#axiomsClean store_registers
#axiomsClean step_register_frame
#axiomsClean run_register_frame
end
end VeriTile.Triton.FP.Structural
