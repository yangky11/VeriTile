import VeriTile.Triton.Float.SourceTracePermission

/-! Invariant introduction for the existing Structural loop write-permission judgments.

The invariant concerns the state immediately before binding the current loop
index. Each step proves permissions of the actual body at that bound state and
preserves the invariant after the actual successful `run`. These lemmas do not
provide successful execution: public IO still proves that separately. No custom
executor is installed in the source semantics.
-/
namespace VeriTile.Triton.FP.Structural.Permission
noncomputable section

/-- A natural counted-loop invariant follows the actual body successor. -/
theorem counted_of_invariant {α : Type} [Inhabited α] (M : Algebra α)
    (ordinary atomic : RegionName → Nat → Prop) (idx : RegName) (stop : Nat)
    (body : List ComputeStmt) (P : Nat → State α → Prop)
    (bodyPermitted : ∀ q, q < stop → ∀ t, P q t →
      trace M ordinary atomic body (t.setReg idx .nat [] (fun _ => q)))
    (preserved : ∀ q, q < stop → ∀ t, P q t → ∀ u,
      run M body (t.setReg idx .nat [] (fun _ => q)) = some u → P (q + 1) u)
    (start : Nat) (s : State α) (initial : P start s) :
    counted M ordinary atomic idx start stop body s := by
  rw [counted_unfold]
  split
  next active =>
    refine ⟨bodyPermitted start active s initial, ?_⟩
    cases ran : run M body (s.setReg idx .nat [] (fun _ => start)) with
    | none => trivial
    | some t =>
      exact counted_of_invariant M ordinary atomic idx stop body P bodyPermitted preserved
        (start + 1) t (preserved start active s initial t ran)
  next => trivial
termination_by stop - start
decreasing_by omega

/-- A natural strided-loop invariant. Zero stride and empty intervals retain
the evaluator's no-iteration behavior without a body obligation. -/
theorem natural_of_invariant {α : Type} [Inhabited α] (M : Algebra α)
    (ordinary atomic : RegionName → Nat → Prop) (idx : RegName) (stop stride : Nat)
    (body : List ComputeStmt) (P : Nat → State α → Prop)
    (bodyPermitted : ∀ q, q < stop → ∀ t, P q t →
      trace M ordinary atomic body (t.setReg idx .nat [] (fun _ => q)))
    (preserved : ∀ q, q < stop → ∀ t, P q t → ∀ u,
      run M body (t.setReg idx .nat [] (fun _ => q)) = some u → P (q + stride) u)
    (start : Nat) (s : State α) (initial : P start s) :
    natural M ordinary atomic idx start stop stride body s := by
  rw [natural_unfold]
  split
  next => trivial
  next nonzero =>
    split
    next active =>
      refine ⟨bodyPermitted start active s initial, ?_⟩
      cases ran : run M body (s.setReg idx .nat [] (fun _ => start)) with
      | none => trivial
      | some t =>
        exact natural_of_invariant M ordinary atomic idx stop stride body P bodyPermitted preserved
          (start + stride) t (preserved start active s initial t ran)
    next => trivial
termination_by stop - start
decreasing_by omega

/-- Signed loop positions retain the signed index register, positive natural
stride and exact predecessor/successor states of `integer`. -/
theorem integer_of_invariant {α : Type} [Inhabited α] (M : Algebra α)
    (ordinary atomic : RegionName → Nat → Prop) (idx : RegName) (stop : Int) (stride : Nat)
    (body : List ComputeStmt) (P : Int → State α → Prop)
    (bodyPermitted : ∀ q, q < stop → ∀ t, P q t →
      trace M ordinary atomic body (t.setReg idx .int [] (fun _ => q)))
    (preserved : ∀ q, q < stop → ∀ t, P q t → ∀ u,
      run M body (t.setReg idx .int [] (fun _ => q)) = some u → P (q + stride) u)
    (start : Int) (s : State α) (initial : P start s) :
    integer M ordinary atomic idx start stop stride body s := by
  rw [integer_unfold]
  split
  next => trivial
  next nonzero =>
    split
    next active =>
      refine ⟨bodyPermitted start active s initial, ?_⟩
      cases ran : run M body (s.setReg idx .int [] (fun _ => start)) with
      | none => trivial
      | some t =>
        exact integer_of_invariant M ordinary atomic idx stop stride body P bodyPermitted preserved
          (start + stride) t (preserved start active s initial t ran)
    next => trivial
termination_by (stop - start).toNat
decreasing_by omega

#axiomsClean counted_of_invariant
#axiomsClean natural_of_invariant
#axiomsClean integer_of_invariant

end
end VeriTile.Triton.FP.Structural.Permission
