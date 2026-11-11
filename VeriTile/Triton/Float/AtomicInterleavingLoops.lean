import VeriTile.Triton.Float.AtomicInterleavingCompletion

/-! Successful supported bodies complete through real control-stack ticks.
The loop induction preserves captured bounds and the exact bound register. -/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

def BodyCompletes (M : Algebra α) (body : List ComputeStmt) : Prop :=
  ∀ initial final, Structural.run M body initial = some final →
    (Local.mk (commands body) initial).Advances M ⟨[],final⟩

theorem body_completes (M : Algebra α) (body : List ComputeStmt)
    (elements : ∀ statement ∈ body, ∀ initial final, step M statement initial = some final →
      (Local.mk [.source statement] initial).Advances M ⟨[],final⟩) : BodyCompletes M body := by
  intro initial final ran
  induction body generalizing initial with
  | nil =>
      simp only [Structural.run,Option.some.injEq] at ran
      subst final
      exact Relation.ReflTransGen.refl
  | cons statement rest ih =>
      rw [Structural.run] at ran
      obtain ⟨middle,first,last⟩ := Option.bind_eq_some_iff.mp ran
      have bodyRan := (elements statement (List.mem_cons_self) initial middle first).append M (commands rest)
      exact bodyRan.trans (ih (fun statement inside => elements statement (List.mem_cons_of_mem _ inside)) middle last)

theorem counted_completes (M : Algebra α) (index : RegName) (current stop : Nat) (body : List ComputeStmt)
    (complete : BodyCompletes M body) (initial final : State α)
    (ran : loop M index current stop body initial = some final) :
    (Local.mk [.counted index current stop body] initial).Advances M ⟨[],final⟩ := by
  by_cases active : current < stop
  · rw [loop,ite_eq_left active] at ran
    obtain ⟨middle,first,last⟩ := Option.bind_eq_some_iff.mp ran
    have head : (Local.mk [.counted index current stop body] initial).tick M initial.mem =
        some ⟨commands body ++ [.counted index (current+1) stop body],
          initial.setReg index .nat [] (fun _ => current)⟩ := by simp [Local.tick,active]
    have bodyRan := (complete _ _ first).append M [.counted index (current+1) stop body]
    exact (Local.Advances.single M head).trans (bodyRan.trans
      (counted_completes M index (current+1) stop body complete middle final last))
  · rw [loop,ite_eq_right active] at ran
    have ran := Option.some.inj ran
    subst final
    exact Local.Advances.single M (by simp [Local.tick,active])
termination_by stop-current
decreasing_by omega

theorem natural_completes (M : Algebra α) (index : RegName) (current stop stride : Nat) (body : List ComputeStmt)
    (complete : BodyCompletes M body) (initial final : State α)
    (ran : range M index current stop stride body initial = some final) :
    (Local.mk [.natural index current stop stride body] initial).Advances M ⟨[],final⟩ := by
  by_cases zero : stride = 0
  · rw [range,ite_eq_left zero] at ran
    have ran := Option.some.inj ran
    subst final
    exact Local.Advances.single M (by simp [Local.tick,zero])
  · by_cases active : current < stop
    · rw [range,ite_eq_right zero,ite_eq_left active] at ran
      obtain ⟨middle,first,last⟩ := Option.bind_eq_some_iff.mp ran
      have head : (Local.mk [.natural index current stop stride body] initial).tick M initial.mem =
          some ⟨commands body ++ [.natural index (current+stride) stop stride body],
            initial.setReg index .nat [] (fun _ => current)⟩ := by
        simp [Local.tick,zero,Nat.not_le.mpr active]
      have bodyRan := (complete _ _ first).append M [.natural index (current+stride) stop stride body]
      exact (Local.Advances.single M head).trans (bodyRan.trans
        (natural_completes M index (current+stride) stop stride body complete middle final last))
    · rw [range,ite_eq_right zero,ite_eq_right active] at ran
      have ran := Option.some.inj ran
      subst final
      exact Local.Advances.single M (by simp [Local.tick,Nat.le_of_not_gt active])
termination_by stop-current
decreasing_by omega

theorem integer_completes (M : Algebra α) (index : RegName) (current stop : Int) (stride : Nat)
    (body : List ComputeStmt) (complete : BodyCompletes M body) (initial final : State α)
    (ran : rangeInt M index current stop stride body initial = some final) :
    (Local.mk [.integer index current stop stride body] initial).Advances M ⟨[],final⟩ := by
  by_cases zero : stride = 0
  · rw [rangeInt,ite_eq_left zero] at ran
    have ran := Option.some.inj ran
    subst final
    exact Local.Advances.single M (by simp [Local.tick,zero])
  · by_cases active : current < stop
    · rw [rangeInt,ite_eq_right zero,ite_eq_left active] at ran
      obtain ⟨middle,first,last⟩ := Option.bind_eq_some_iff.mp ran
      have head : (Local.mk [.integer index current stop stride body] initial).tick M initial.mem =
          some ⟨commands body ++ [.integer index (current+stride) stop stride body],
            initial.setReg index .int [] (fun _ => current)⟩ := by
        simp [Local.tick,zero,Int.not_le.mpr active]
      have bodyRan := (complete _ _ first).append M [.integer index (current+stride) stop stride body]
      exact (Local.Advances.single M head).trans (bodyRan.trans
        (integer_completes M index (current+stride) stop stride body complete middle final last))
    · rw [rangeInt,ite_eq_right zero,ite_eq_right active] at ran
      have ran := Option.some.inj ran
      subst final
      exact Local.Advances.single M (by simp [Local.tick,Int.le_of_not_gt active])
termination_by (stop-current).toNat
decreasing_by omega

#axiomsClean body_completes
#axiomsClean counted_completes
#axiomsClean natural_completes
#axiomsClean integer_completes
end
end VeriTile.Triton.FP.Structural.Interleaved
