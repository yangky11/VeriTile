import VeriTile.Triton.Float.AtomicInterleavingCompletion

/-! The scheduler's explicit control stack carries the existing source trace
safety predicate. Expanding a loop does not introduce a new safety assumption. -/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

def Command.Safe (M : Algebra α) (bounds : RegionName → Nat) : Command → State α → Prop
  | .source statement, state => Safety.stepSafe M bounds statement state
  | .counted index current stop body, state => Safety.loopSafe M bounds index current stop body state
  | .natural index current stop stride body, state => Safety.rangeSafe M bounds index current stop stride body state
  | .integer index current stop stride body, state => Safety.rangeIntSafe M bounds index current stop stride body state

def evaluateSafe (M : Algebra α) (bounds : RegionName → Nat) : List Command → State α → Prop
  | [], _ => True
  | command :: rest, state => command.Safe M bounds state ∧
      ∀ next, command.eval M state = some next → evaluateSafe M bounds rest next

theorem evaluateSafe_commands (M : Algebra α) (bounds : RegionName → Nat)
    (body : List ComputeStmt) (state : State α) :
    evaluateSafe M bounds (commands body) state ↔ Safety.traceSafeList M bounds body state := by
  induction body generalizing state with
  | nil => simp only [commands,List.map_nil,evaluateSafe,Safety.traceSafeList]
  | cons statement rest ih =>
      simp only [commands,List.map_cons,evaluateSafe,Command.Safe,Command.eval,Safety.traceSafeList]
      simp only [commands] at ih
      cases advanced : step M statement state <;> simp [ih]

theorem evaluateSafe_append (M : Algebra α) (bounds : RegionName → Nat)
    (first rest : List Command) (state : State α) :
    evaluateSafe M bounds (first ++ rest) state ↔
      evaluateSafe M bounds first state ∧
        ∀ next, evaluate M first state = some next → evaluateSafe M bounds rest next := by
  induction first generalizing state with
  | nil => simp [evaluateSafe,evaluate]
  | cons command tail ih =>
      simp only [List.cons_append,evaluateSafe,evaluate]
      cases advanced : command.eval M state <;> simp [ih,and_assoc]

theorem evaluateSafe_body (M : Algebra α) (bounds : RegionName → Nat)
    (body : List ComputeStmt) (rest : List Command) (state : State α) :
    evaluateSafe M bounds (commands body ++ rest) state ↔
      Safety.traceSafeList M bounds body state ∧
        ∀ next, Structural.run M body state = some next → evaluateSafe M bounds rest next := by
  rw [evaluateSafe_append,evaluateSafe_commands,evaluate_commands]

#axiomsClean evaluateSafe_commands
#axiomsClean evaluateSafe_append
#axiomsClean evaluateSafe_body
end
end VeriTile.Triton.FP.Structural.Interleaved
