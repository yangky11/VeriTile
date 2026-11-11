import VeriTile.Triton.Float.Control
import VeriTile.Meta.StatementAudit

/-! Signed source-loop invariant with a positive natural stride. Negative
starting indices are retained, and the final index may overshoot the stop. -/
namespace VeriTile.Triton.FP.Structural
variable {α : Type} [Inhabited α] (M : Algebra α)

theorem rangeInt_done (index : RegName) (current stop : Int) (stride : Nat) (body : List ComputeStmt)
    (state : State α) (done : stop ≤ current) : rangeInt M index current stop stride body state = some state := by
  rw [rangeInt]
  simp [Int.not_lt.mpr done]

theorem rangeInt_step (index : RegName) (current stop : Int) (stride : Nat) (body : List ComputeStmt)
    (state : State α) (positive : stride ≠ 0) (active : current < stop) :
    rangeInt M index current stop stride body state =
      (run M body (state.setReg index .int [] (fun _ => current))).bind
        (rangeInt M index (current+stride) stop stride body) := by
  rw [rangeInt]
  simp [positive,active]

theorem rangeInt_invariant {index : RegName} {stop : Int} {stride : Nat} {body : List ComputeStmt}
    {P : Int → State α → Prop} (positive : stride ≠ 0)
    (advance : ∀ i state, i < stop → P i state →
      ∃ next, run M body (state.setReg index .int [] (fun _ => i)) = some next ∧ P (i+stride) next)
    (current : Int) (state : State α) (ready : P current state) :
    ∃ last final, rangeInt M index current stop stride body state = some final ∧ stop ≤ last ∧ P last final := by
  have key : ∀ distance i state, (stop-i).toNat = distance → P i state →
      ∃ last final, rangeInt M index i stop stride body state = some final ∧ stop ≤ last ∧ P last final := by
    intro distance
    induction distance using Nat.strong_induction_on with
    | h distance ih =>
        intro i state measure ready
        by_cases done : stop ≤ i
        · exact ⟨i,state,rangeInt_done M index i stop stride body state done,done,ready⟩
        · have active : i < stop := by omega
          obtain ⟨next,ran,preserved⟩ := advance i state active ready
          obtain ⟨last,final,rest,finished,result⟩ := ih (stop-(i+stride)).toNat (by omega)
            (i+stride) next rfl preserved
          refine ⟨last,final,?_,finished,result⟩
          rw [rangeInt_step M index i stop stride body state positive active,ran]
          exact rest
  exact key (stop-current).toNat current state rfl ready

#axiomsClean rangeInt_done
#axiomsClean rangeInt_step
#axiomsClean rangeInt_invariant
end VeriTile.Triton.FP.Structural
