import VeriTile.Triton.Float.SignedControl
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! An exact source-loop visit supplies a selected observable, and subsequent
iterations preserve it. This composes arbitrary body proofs without replacing
the source loop or assuming a whole-loop execution callback. -/
namespace VeriTile.Triton.FP.Structural
variable {α β : Type} [Inhabited α] (M : Algebra α)

theorem rangeInt_readback (index : RegName) (start stop : Int) (stride : Nat)
    (positive : 0 < stride) (body : List ComputeStmt)
    (P : State α → Prop) (observe : State α → β) (target : Nat) (value : β)
    (inside : start + (target : Int)*stride < stop)
    (advance : ∀ (n : Nat) state, start + (n : Int)*stride < stop → P state →
      ∃ next, run M body (state.setReg index .int [] (fun _ => start + (n : Int)*stride)) = some next ∧
        P next ∧ (n = target → observe next = value) ∧
        (target < n → observe next = observe state))
    (initial : State α) (ready : P initial) :
    ∃ final, rangeInt M index start stop stride body initial = some final ∧ P final ∧ observe final = value := by
  let Q := fun i state => ∃ n : Nat, i = start + (n : Int)*stride ∧ P state ∧
    (target < n → observe state = value)
  have step : ∀ i state, i < stop → Q i state →
      ∃ next, run M body (state.setReg index .int [] (fun _ => i)) = some next ∧ Q (i+stride) next := by
    intro i state active ⟨n,position,invariant,observed⟩
    subst i
    obtain ⟨next,ran,preserved,written,framed⟩ := advance n state active invariant
    refine ⟨next,ran,n+1,?_,preserved,?_⟩
    · simp only [Nat.cast_add,Nat.cast_one]
      ring
    · intro visited
      by_cases same : n = target
      · exact written same
      · have earlier : target < n := by omega
        exact (framed earlier).trans (observed earlier)
  obtain ⟨last,final,ran,finished,n,position,preserved,observed⟩ := rangeInt_invariant M
    (P := Q) (Nat.ne_of_gt positive) step start initial ⟨0,by simp,ready,by omega⟩
  refine ⟨final,ran,preserved,observed ?_⟩
  by_contra notVisited
  have order : (n : Int) ≤ target := by exact_mod_cast (Nat.le_of_not_gt notVisited)
  have strideNonnegative : (0 : Int) ≤ stride := Int.natCast_nonneg _
  have products := mul_le_mul_of_nonneg_right order strideNonnegative
  omega

#axiomsClean rangeInt_readback
end VeriTile.Triton.FP.Structural
