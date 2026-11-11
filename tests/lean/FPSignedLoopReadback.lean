import VeriTile.Triton.Float.SignedLoopReadback

/-! Signed-loop readback with a negative starting index, non-unit stride and
an overshooting exit. A real conditional source statement writes only on the
first visit and later source iterations leave the selected register intact. -/
namespace FPSignedLoopReadbackTests
open VeriTile.Triton FP.Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false

def body : List ComputeStmt := [
  .ifThenElse (.lt .int .nil (.ref .int [] "i") (.constInt (-6)))
    [.assign .real [] "marked" (.alg (.const 42))] []]

theorem selected_visit {α : Type} [Inhabited α] (M : Algebra α) (initial : State α) :
    ∃ final, rangeInt M "i" (-7) 2 4 body initial = some final ∧
      final.regs .real [] "marked" = some (fun _ => M.literal none .real 42) := by
  have advance : ∀ (n : Nat) (state : State α), (-7 : Int) + (n : Int)*4 < 2 → True →
      ∃ next, run M body (state.setReg "i" .int [] (fun _ => (-7 : Int) + (n : Int)*4)) = some next ∧
        True ∧ (n = 0 → next.regs .real [] "marked" = some (fun _ => M.literal none .real 42)) ∧
        (0 < n → next.regs .real [] "marked" = state.regs .real [] "marked") := by
    intro n state _ _
    by_cases first : n = 0
    · subst n
      refine ⟨(state.setReg "i" .int [] (fun _ => -7)).setReg "marked" .real []
        (fun _ => M.literal none .real 42),?_,True.intro,?_,by omega⟩
      · simp [body,run,step,evalExpr,evalOp_unfold,numericLt,bop]
      · intro _; simp
    · have later : ¬ ((-7 : Int) + (n : Int)*4 < -6) := by omega
      refine ⟨state.setReg "i" .int [] (fun _ => (-7 : Int) + (n : Int)*4),?_,True.intro,
        by simp [first],?_⟩
      · simp [body,run,step,evalExpr,evalOp_unfold,numericLt,bop,later]
      · intro _; simp
  obtain ⟨final,ran,_,readback⟩ := rangeInt_readback M "i" (-7) 2 4 (by decide) body
    (fun _ => True) (fun state => state.regs .real [] "marked") 0
    (some (fun _ => M.literal none .real 42)) (by norm_num) advance initial True.intro
  exact ⟨final,ran,readback⟩

#axiomsClean selected_visit
end
end FPSignedLoopReadbackTests
