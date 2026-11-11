import VeriTile.Triton.Float.AtomicInterleavingCompletion
import VeriTile.Triton.Float.SourceTracePermission

/-! The scheduler's explicit control stack carries the existing source write
permission predicate. Expanding a loop does not introduce a new ownership assumption. -/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

def Command.Permissions (M : Algebra α) (ordinary atomic : RegionName → Nat → Prop) : Command → State α → Prop
  | .source statement, state => Permission.statement M ordinary atomic statement state
  | .counted index current stop body, state => Permission.counted M ordinary atomic index current stop body state
  | .natural index current stop stride body, state => Permission.natural M ordinary atomic index current stop stride body state
  | .integer index current stop stride body, state => Permission.integer M ordinary atomic index current stop stride body state

def evaluatePermitted (M : Algebra α) (ordinary atomic : RegionName → Nat → Prop) : List Command → State α → Prop
  | [], _ => True
  | command :: rest, state => command.Permissions M ordinary atomic state ∧
      ∀ next, command.eval M state = some next → evaluatePermitted M ordinary atomic rest next

theorem evaluatePermitted_commands (M : Algebra α) (ordinary atomic : RegionName → Nat → Prop)
    (body : List ComputeStmt) (state : State α) :
    evaluatePermitted M ordinary atomic (commands body) state ↔ Permission.trace M ordinary atomic body state := by
  induction body generalizing state with
  | nil => simp only [commands,List.map_nil,evaluatePermitted,Permission.trace]
  | cons statement rest ih =>
      simp only [commands,List.map_cons,evaluatePermitted,Command.Permissions,Command.eval,Permission.trace]
      simp only [commands] at ih
      cases advanced : step M statement state <;> simp [ih]

theorem evaluatePermitted_append (M : Algebra α) (ordinary atomic : RegionName → Nat → Prop)
    (first rest : List Command) (state : State α) :
    evaluatePermitted M ordinary atomic (first ++ rest) state ↔
      evaluatePermitted M ordinary atomic first state ∧
        ∀ next, evaluate M first state = some next → evaluatePermitted M ordinary atomic rest next := by
  induction first generalizing state with
  | nil => simp [evaluatePermitted,evaluate]
  | cons command tail ih =>
      simp only [List.cons_append,evaluatePermitted,evaluate]
      cases advanced : command.eval M state <;> simp [ih,and_assoc]

theorem evaluatePermitted_body (M : Algebra α) (ordinary atomic : RegionName → Nat → Prop)
    (body : List ComputeStmt) (rest : List Command) (state : State α) :
    evaluatePermitted M ordinary atomic (commands body ++ rest) state ↔
      Permission.trace M ordinary atomic body state ∧
        ∀ next, Structural.run M body state = some next → evaluatePermitted M ordinary atomic rest next := by
  rw [evaluatePermitted_append,evaluatePermitted_commands,evaluate_commands]

#axiomsClean evaluatePermitted_commands
#axiomsClean evaluatePermitted_append
#axiomsClean evaluatePermitted_body
end
end VeriTile.Triton.FP.Structural.Interleaved
