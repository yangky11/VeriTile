import VeriTile.Triton.Float.SourceTracePermissionComposition
import VeriTile.Triton.Float.SourceTracePermissionLoops

/-! Read-only computations have no write-permission obligations. This reuses
the structural region check for arbitrary source loops and branches. -/
namespace VeriTile.Triton.FP.Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

private theorem no_access_outside (access : MemAccess dtype shape) :
    ¬ accessOutside (fun _ => True) access := by cases access <;> simp [accessOutside]

private theorem algReadOnly_permission (M : Algebra α) (ordinary atomic : RegionName → Nat → Prop)
    (statement : Stmt) (confined : algReadOnly (fun _ => True) statement) (state : State α) :
    algWritePermitted M ordinary atomic statement state := by
  unfold algReadOnly at confined
  split at confined
  · trivial
  · exact False.elim (no_access_outside _ confined)
  · exact False.elim (no_access_outside _ confined)
  · exact False.elim (no_access_outside _ confined)
  · contradiction

mutual
  theorem readOnly_statement_permission (M : Algebra α) (ordinary atomic : RegionName → Nat → Prop)
      (statement : ComputeStmt) (confined : readOnly (fun _ => True) statement) (state : State α) :
      Permission.statement M ordinary atomic statement state := by
    cases selectedStatement : statement with
    | alg statement =>
        simp only [selectedStatement,readOnly] at confined
        simp only [selectedStatement,Permission.statement,leafWritePermitted]
        exact algReadOnly_permission M ordinary atomic statement confined state
    | assign => simp [selectedStatement,Permission.statement,leafWritePermitted]
    | store dtype shape access expression mask | atomicAdd dtype shape access expression mask =>
        simp only [selectedStatement,readOnly] at confined
        exact False.elim (no_access_outside access confined)
    | atomicRMW operation dtype shape access expression result mask order =>
        cases result <;> cases order <;> simp only [selectedStatement,readOnly] at confined
        all_goals first | contradiction | exact False.elim (no_access_outside access confined)
    | forLoop index stop body =>
        simp only [selectedStatement,readOnly] at confined
        simp only [selectedStatement,Permission.statement]
        apply Permission.counted_of_invariant M ordinary atomic index stop body (fun _ _ => True)
        · intro _ _ current _
          exact readOnly_trace_permission M ordinary atomic body confined _
        · intros; trivial
        · trivial
    | forRange index start stop stride body =>
        simp only [selectedStatement,readOnly] at confined
        simp only [selectedStatement,Permission.statement]
        apply Permission.natural_of_invariant M ordinary atomic index stop stride body (fun _ _ => True)
        · intro _ _ current _
          exact readOnly_trace_permission M ordinary atomic body confined _
        · intros; trivial
        · trivial
    | forRangeDyn index start stop stride body =>
        simp only [selectedStatement,readOnly] at confined
        simp only [selectedStatement,Permission.statement]
        split
        · apply Permission.natural_of_invariant M ordinary atomic index _ _ body (fun _ _ => True)
          · intro _ _ current _
            exact readOnly_trace_permission M ordinary atomic body confined _
          · intros; trivial
          · trivial
        · trivial
    | forRangeInt index start stop stride body =>
        simp only [selectedStatement,readOnly] at confined
        simp only [selectedStatement,Permission.statement]
        split
        · apply Permission.integer_of_invariant M ordinary atomic index _ _ body (fun _ _ => True)
          · intro _ _ current _
            exact readOnly_trace_permission M ordinary atomic body confined _
          · intros; trivial
          · trivial
        · trivial
    | ifThen condition body =>
        simp only [selectedStatement,readOnly] at confined
        simp only [selectedStatement,Permission.statement]
        split
        · split
          · exact readOnly_trace_permission M ordinary atomic body confined state
          · trivial
        · trivial
    | ifThenElse condition yes no =>
        simp only [selectedStatement,readOnly] at confined
        simp only [selectedStatement,Permission.statement]
        split
        · split
          · exact readOnly_trace_permission M ordinary atomic yes confined.1 state
          · exact readOnly_trace_permission M ordinary atomic no confined.2 state
        · trivial
    | effectMarker => simp [selectedStatement,readOnly] at confined
  termination_by sizeOf statement
  decreasing_by all_goals (simp_all <;> omega)

  theorem readOnly_trace_permission (M : Algebra α) (ordinary atomic : RegionName → Nat → Prop)
      (body : List ComputeStmt) (confined : readOnlyBody (fun _ => True) body) (state : State α) :
      Permission.trace M ordinary atomic body state := by
    cases selectedBody : body with
    | nil => simp [Permission.trace]
    | cons statement rest =>
        simp only [selectedBody,readOnlyBody] at confined
        apply Permission.trace_cons_intro
        · exact readOnly_statement_permission M ordinary atomic statement confined.1 state
        · intro next _
          exact readOnly_trace_permission M ordinary atomic rest confined.2 next
  termination_by sizeOf body
  decreasing_by all_goals (simp_all <;> omega)
end

#axiomsClean readOnly_statement_permission
#axiomsClean readOnly_trace_permission
end
end VeriTile.Triton.FP.Structural
