import VeriTile.Triton.Float.SignedLoopWriteTrace

/-! The actual signed-loop visit sequence is independent of numeric operands.
Its flat-map gives the proved primitive stream, retaining zero-stride semantics,
negative starts, non-unit strides and overshooting exits. -/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
variable {α : Type}

def integerVisits (current stop : Int) (stride : Nat) : List Int :=
  if stride = 0 then []
  else if current < stop then current :: integerVisits (current+stride) stop stride
  else []
termination_by (stop-current).toNat
decreasing_by omega

theorem integerEvents_visits (current stop : Int) (stride : Nat) (events : Int → List (MemoryWrite α)) :
    integerEvents current stop stride events = (integerVisits current stop stride).flatMap events := by
  by_cases zero : stride = 0
  · rw [integerEvents,integerVisits,ite_eq_left zero,ite_eq_left zero]; rfl
  · by_cases active : current < stop
    · rw [integerEvents,integerVisits,ite_eq_right zero,ite_eq_right zero,ite_eq_left active,ite_eq_left active,
        List.flatMap_cons,integerEvents_visits (current+stride) stop stride events]
    · rw [integerEvents,integerVisits,ite_eq_right zero,ite_eq_right zero,ite_eq_right active,ite_eq_right active]; rfl
termination_by (stop-current).toNat
decreasing_by omega

theorem integerVisits_bounds (current stop : Int) (stride : Nat) (i : Int)
    (member : i ∈ integerVisits current stop stride) : current ≤ i ∧ i < stop := by
  by_cases zero : stride = 0
  · rw [integerVisits,ite_eq_left zero] at member; contradiction
  · by_cases active : current < stop
    · rw [integerVisits,ite_eq_right zero,ite_eq_left active] at member
      rcases List.mem_cons.mp member with same | later
      · subst i; exact ⟨le_refl _,active⟩
      · have bounded := integerVisits_bounds (current+stride) stop stride i later
        exact ⟨by omega,bounded.2⟩
    · rw [integerVisits,ite_eq_right zero,ite_eq_right active] at member; contradiction
termination_by (stop-current).toNat
decreasing_by omega

#axiomsClean integerEvents_visits
#axiomsClean integerVisits_bounds
end
end VeriTile.Triton.FP.Structural.Interleaved
