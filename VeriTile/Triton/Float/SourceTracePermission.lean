import VeriTile.Triton.Float.SourceWritePermission

/-! Write permissions follow the actual sequential source execution, including
captured loop bounds and intermediate states. They can certify noncontiguous
worker footprints without replacing a source program by a bespoke formula. -/
namespace VeriTile.Triton.FP.Structural.Permission
noncomputable section
set_option backward.isDefEq.respectTransparency false

mutual
/-- Write permissions of one source statement at the state in which it executes.
Branches and loops use the actual evaluator; unsupported effects fail closed. -/
def statement {α : Type} [Inhabited α] (M : Algebra α)
    (ordinary atomic : RegionName → Nat → Prop) : ComputeStmt → State α → Prop
  | .forLoop idx n body, s => counted M ordinary atomic idx 0 n body s
  | .forRange idx start stop stride body, s => natural M ordinary atomic idx start stop stride body s
  | .forRangeDyn idx start stop stride body, s =>
      match evalOp M none start s, evalOp M none stop s, evalOp M none stride s with
      | some a, some b, some d => natural M ordinary atomic idx (a PUnit.unit) (b PUnit.unit) (d PUnit.unit) body s
      | _, _, _ => True
  | .forRangeInt idx start stop stride body, s =>
      match evalOp M none start s, evalOp M none stop s, evalOp M none stride s with
      | some a, some b, some d => integer M ordinary atomic idx (a PUnit.unit) (b PUnit.unit) (d PUnit.unit) body s
      | _, _, _ => True
  | .ifThen cond body, s =>
      match evalOp M none cond s with
      | some c => if c PUnit.unit then trace M ordinary atomic body s else True
      | none => True
  | .ifThenElse cond yes no, s =>
      match evalOp M none cond s with
      | some c => if c PUnit.unit then trace M ordinary atomic yes s else trace M ordinary atomic no s
      | none => True
  | statement, s => leafWritePermitted M ordinary atomic statement s
termination_by st _ => (sizeOf st, 0)
decreasing_by
  all_goals simp_wf
  all_goals (try omega)
  all_goals (have : 0 < sizeOf idx := by cases idx; simp)
  all_goals omega

/-- Each write is checked in its actual predecessor state. A failed step
has no successor; public IO additionally proves a successful execution. -/
def trace {α : Type} [Inhabited α] (M : Algebra α)
    (ordinary atomic : RegionName → Nat → Prop) : List ComputeStmt → State α → Prop
  | [], _ => True
  | st :: rest, s => statement M ordinary atomic st s ∧
      match step M st s with
      | some t => trace M ordinary atomic rest t
      | none => True
termination_by code _ => (sizeOf code, 0)
decreasing_by all_goals (simp_wf; omega)

/-- Counted-loop safety follows the existing loop's exact index sequence. -/
def counted {α : Type} [Inhabited α] (M : Algebra α)
    (ordinary atomic : RegionName → Nat → Prop) (idx : RegName) (start stop : Nat)
    (body : List ComputeStmt) (s : State α) : Prop :=
  if start < stop then
    trace M ordinary atomic body (s.setReg idx .nat [] (fun _ => start)) ∧
    match run M body (s.setReg idx .nat [] (fun _ => start)) with
    | some t => counted M ordinary atomic idx (start + 1) stop body t
    | none => True
  else True
termination_by (sizeOf body + 1, stop - start)
decreasing_by all_goals omega

/-- A zero stride or empty natural interval makes no body access. -/
def natural {α : Type} [Inhabited α] (M : Algebra α)
    (ordinary atomic : RegionName → Nat → Prop) (idx : RegName) (cur stop stride : Nat)
    (body : List ComputeStmt) (s : State α) : Prop :=
  if stride = 0 then True else if cur < stop then
    trace M ordinary atomic body (s.setReg idx .nat [] (fun _ => cur)) ∧
    match run M body (s.setReg idx .nat [] (fun _ => cur)) with
    | some t => natural M ordinary atomic idx (cur + stride) stop stride body t
    | none => True
  else True
termination_by (sizeOf body + 1, stop - cur)
decreasing_by all_goals omega

/-- Signed dynamic ranges retain their signed indices and actual successor states. -/
def integer {α : Type} [Inhabited α] (M : Algebra α)
    (ordinary atomic : RegionName → Nat → Prop) (idx : RegName) (cur stop : Int) (stride : Nat)
    (body : List ComputeStmt) (s : State α) : Prop :=
  if stride = 0 then True else if cur < stop then
    trace M ordinary atomic body (s.setReg idx .int [] (fun _ => cur)) ∧
    match run M body (s.setReg idx .int [] (fun _ => cur)) with
    | some t => integer M ordinary atomic idx (cur + stride) stop stride body t
    | none => True
  else True
termination_by (sizeOf body + 1, (stop - cur).toNat)
decreasing_by all_goals omega
end

abbrev statement_unfold := @statement.eq_def
abbrev trace_unfold := @trace.eq_def
abbrev counted_unfold := @counted.eq_def
abbrev natural_unfold := @natural.eq_def
abbrev integer_unfold := @integer.eq_def

end
end VeriTile.Triton.FP.Structural.Permission
