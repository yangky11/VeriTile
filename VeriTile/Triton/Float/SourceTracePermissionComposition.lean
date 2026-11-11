import VeriTile.Triton.Float.SourceTracePermission

/-! Permission certificates compose through actual intermediate source states. -/
namespace VeriTile.Triton.FP.Structural.Permission
noncomputable section

@[simp] theorem trace_nil {α : Type} [Inhabited α] (M : Algebra α)
    (ordinary atomic : RegionName → Nat → Prop) (s : State α) : trace M ordinary atomic [] s := by
  rw [trace]
  trivial

theorem trace_cons {α : Type} [Inhabited α] (M : Algebra α)
    (ordinary atomic : RegionName → Nat → Prop) (st : ComputeStmt) (rest : List ComputeStmt) (s : State α) :
    trace M ordinary atomic (st :: rest) s ↔ statement M ordinary atomic st s ∧
      ∀ t, step M st s = some t → trace M ordinary atomic rest t := by
  simp only [trace]
  cases h : step M st s <;> simp

theorem trace_cons_intro {α : Type} [Inhabited α] {M : Algebra α}
    {ordinary atomic : RegionName → Nat → Prop} {st : ComputeStmt} {rest : List ComputeStmt} {s : State α}
    (head : statement M ordinary atomic st s)
    (tail : ∀ t, step M st s = some t → trace M ordinary atomic rest t) :
    trace M ordinary atomic (st :: rest) s :=
  (trace_cons M ordinary atomic st rest s).mpr ⟨head, tail⟩

/-- Prefix/suffix composition shares the actual intermediate execution state. -/
theorem trace_append {α : Type} [Inhabited α] (M : Algebra α)
    (ordinary atomic : RegionName → Nat → Prop) (before after : List ComputeStmt) (s : State α) :
    trace M ordinary atomic (before ++ after) s ↔
      trace M ordinary atomic before s ∧
      ∀ t, run M before s = some t → trace M ordinary atomic after t := by
  induction before generalizing s with
  | nil => simp [run]
  | cons st rest ih =>
      cases h : step M st s <;>
        simp [trace, run, h, ih, and_assoc]

/-- Checked straight-line introduction with a known actual successor. -/
theorem trace_cons_of_step {α : Type} [Inhabited α] {M : Algebra α}
    {ordinary atomic : RegionName → Nat → Prop} {st : ComputeStmt} {rest : List ComputeStmt} {s t : State α}
    (head : statement M ordinary atomic st s) (executed : step M st s = some t)
    (tail : trace M ordinary atomic rest t) : trace M ordinary atomic (st :: rest) s := by
  rw [trace, executed]
  exact ⟨head, tail⟩

#axiomsClean trace_cons
#axiomsClean trace_cons_intro
#axiomsClean trace_append
#axiomsClean trace_cons_of_step
end
end VeriTile.Triton.FP.Structural.Permission
