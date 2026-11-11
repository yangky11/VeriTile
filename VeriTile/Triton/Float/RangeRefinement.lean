import VeriTile.Triton.Float.Control

/-! Relational refinement of actual strided execution to an ordered fold.
The caller supplies the per-iteration connection and exact loop coverage.
No associativity, identity, numerical policy or whole-loop result is assumed. -/
namespace VeriTile.Triton.FP.Structural
noncomputable section

theorem stage_lt_ceil_iff (stop stride stage : Nat) (positive : 0 < stride) :
    stage < (stop+stride-1)/stride ↔ stage*stride < stop := by
  rw [Nat.lt_div_iff_mul_lt positive]
  have equal : stop+stride-1-(stride-1) = stop := by omega
  rw [equal]

/-- Relate the executed source states to a specification state after exactly
`count` stages. Stage `i` binds the original source counter to `i * stride`;
the terminal source counter may overshoot `stop`. -/
theorem range_fold_refines {α β : Type} [Inhabited α] (M : Algebra α)
    (idx : RegName) (stop stride : Nat) (body : List ComputeStmt)
    (relation : State α → β → Prop) (update : β → Nat → β)
    (nonzero : stride ≠ 0)
    (advance : ∀ stage state value, stage*stride < stop → relation state value →
      ∃ next, run M body (state.setReg idx .nat [] (fun _ => stage*stride)) = some next ∧
        relation next (update value stage))
    (start count : Nat) (initial : State α) (value : β)
    (active : ∀ stage, start ≤ stage → stage < start+count → stage*stride < stop)
    (done : stop ≤ (start+count)*stride) (related : relation initial value) :
    ∃ final, range M idx (start*stride) stop stride body initial = some final ∧
      relation final ((List.range' start count).foldl update value) := by
  induction count generalizing start initial value with
  | zero =>
    refine ⟨initial,range_done M idx _ _ _ _ _ (by simpa using done),?_⟩
    simpa using related
  | succ count ih =>
    have hit : start*stride < stop := active start (Nat.le_refl _) (by omega)
    obtain ⟨next,ran,relatedNext⟩ := advance start initial value hit related
    have nextActive : ∀ stage, start+1 ≤ stage → stage < start+1+count → stage*stride < stop := by
      intro stage lower upper
      exact active stage (by omega) (by omega)
    have nextDone : stop ≤ (start+1+count)*stride := by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using done
    obtain ⟨final,finished,result⟩ := ih (start+1) next (update value start) nextActive nextDone relatedNext
    refine ⟨final,?_,?_⟩
    · rw [range_step M idx _ _ _ _ _ nonzero hit,ran]
      simpa only [Option.bind_some,Nat.add_mul,Nat.one_mul] using finished
    · simpa only [List.range'_succ,List.foldl_cons] using result

/-- Zero-based source ranges cover exactly the ceiling-division stage count,
including an empty range and a partial final tile. -/
theorem range_zero_fold_refines {α β : Type} [Inhabited α] (M : Algebra α)
    (idx : RegName) (stop stride : Nat) (body : List ComputeStmt)
    (relation : State α → β → Prop) (update : β → Nat → β) (positive : 0 < stride)
    (advance : ∀ stage state value, stage*stride < stop → relation state value →
      ∃ next, run M body (state.setReg idx .nat [] (fun _ => stage*stride)) = some next ∧
        relation next (update value stage))
    (initial : State α) (value : β) (related : relation initial value) :
    ∃ final, range M idx 0 stop stride body initial = some final ∧
      relation final ((List.range ((stop+stride-1)/stride)).foldl update value) := by
  have done : stop ≤ ((stop+stride-1)/stride)*stride := by
    apply Nat.le_of_not_gt
    intro hit
    exact Nat.lt_irrefl _ ((stage_lt_ceil_iff stop stride _ positive).mpr hit)
  have active : ∀ stage, 0 ≤ stage → stage < 0+(stop+stride-1)/stride → stage*stride < stop := by
    intro stage _ hit
    exact (stage_lt_ceil_iff stop stride stage positive).mp (by simpa using hit)
  simpa only [Nat.zero_mul,Nat.zero_add,List.range_eq_range'] using
    range_fold_refines M idx stop stride body relation update (Nat.ne_of_gt positive) advance
      0 ((stop+stride-1)/stride) initial value active (by simpa using done) related

end
end VeriTile.Triton.FP.Structural
