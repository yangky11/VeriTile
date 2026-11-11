import VeriTile.Triton.Float.AtomicInterleavingTraceComposition

/-! Ordered primitive streams for actual signed source loops. A body proof
may use an invariant to identify its operands; the loop preserves every visit
and its order, including negative starts and overshooting exits. -/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

def integerEvents (current stop : Int) (stride : Nat) (events : Int → List (MemoryWrite α)) : List (MemoryWrite α) :=
  if stride = 0 then []
  else if current < stop then events current ++ integerEvents (current+stride) stop stride events
  else []
termination_by (stop-current).toNat
decreasing_by omega

theorem integer_writeTrace (M : Algebra α) (index : RegName) (current stop : Int) (stride : Nat)
    (body : List ComputeStmt) (events : Int → List (MemoryWrite α)) (P : Int → State α → Prop)
    (advance : ∀ i before after, i < stop → P i before →
      Structural.run M body (before.setReg index .int [] (fun _ => i)) = some after →
      P (i+stride) after ∧
        (Local.mk (commands body) (before.setReg index .int [] (fun _ => i))).WriteAdvances M (events i) ⟨[],after⟩)
    (initial final : State α) (ready : P current initial)
    (ran : rangeInt M index current stop stride body initial = some final) :
    (Local.mk [.integer index current stop stride body] initial).WriteAdvances M
      (integerEvents current stop stride events) ⟨[],final⟩ := by
  by_cases zero : stride = 0
  · rw [rangeInt,ite_eq_left zero] at ran
    have same := Option.some.inj ran
    subst final
    rw [integerEvents,ite_eq_left zero]
    exact Local.WriteAdvances.single M (by simp [Local.tick,zero]) rfl
  · by_cases active : current < stop
    · rw [rangeInt,ite_eq_right zero,ite_eq_left active] at ran
      obtain ⟨middle,first,last⟩ := Option.bind_eq_some_iff.mp ran
      obtain ⟨preserved,traced⟩ := advance current initial middle active ready first
      have head : (Local.mk [.integer index current stop stride body] initial).WriteAdvances M []
          ⟨commands body ++ [.integer index (current+stride) stop stride body],
            initial.setReg index .int [] (fun _ => current)⟩ :=
        Local.WriteAdvances.single M (by simp [Local.tick,zero,Int.not_le.mpr active]) rfl
      have bodyRan := traced.append [.integer index (current+stride) stop stride body]
      have remaining := integer_writeTrace M index (current+stride) stop stride body events P advance middle final preserved last
      have combined := head.trans (bodyRan.trans (by simpa only [Local.append,List.nil_append] using remaining))
      rw [integerEvents,ite_eq_right zero,ite_eq_left active]
      simpa only [List.nil_append] using combined
    · rw [rangeInt,ite_eq_right zero,ite_eq_right active] at ran
      have same := Option.some.inj ran
      subst final
      rw [integerEvents,ite_eq_right zero,ite_eq_right active]
      exact Local.WriteAdvances.single M (by simp [Local.tick,Int.le_of_not_gt active]) rfl
termination_by (stop-current).toNat
decreasing_by omega

#axiomsClean integer_writeTrace
end
end VeriTile.Triton.FP.Structural.Interleaved
