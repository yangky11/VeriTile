import VeriTile.Triton.Float.SignedLoopWriteTrace

/-! Filtering a proved write history to atomic events preserves each worker's
order. Ordinary payload writes can be excluded without reordering atomics. -/
namespace VeriTile.Triton.FP.Structural
noncomputable section
variable {α : Type}

namespace MemoryWrite

def isAtomic : MemoryWrite α → Bool
  | .store .. => false
  | .atomic .. => true

theorem lanes_stores {ι : Type} (indices : List ι) (active : ι → Bool)
    (region : ι → RegionName) (offset : ι → Nat) (value : ι → Cell α) :
    (lanes indices active (fun i => .store (region i) (offset i) (value i))).filter isAtomic = [] := by
  induction indices with
  | nil => rfl
  | cons i rest ih => cases selected : active i <;> simp [lanes,selected,isAtomic] at ih ⊢ <;> exact ih

end MemoryWrite
namespace Interleaved

theorem mem_workerEvents {count : Nat} (events : List (Fin count × MemoryWrite α))
    (worker : Fin count) (event : MemoryWrite α) (member : (worker,event) ∈ events) :
    event ∈ workerEvents events worker :=
  List.mem_filterMap.mpr ⟨(worker,event),member,by simp⟩

theorem workerEvents_filter {count : Nat} (events : List (Fin count × MemoryWrite α))
    (worker : Fin count) (keep : MemoryWrite α → Bool) :
    workerEvents (events.filter (fun entry => keep entry.2)) worker = (workerEvents events worker).filter keep := by
  induction events with
  | nil => rfl
  | cons entry rest ih =>
      by_cases selected : entry.1 = worker
      · cases retained : keep entry.2 <;> simp [workerEvents,selected,retained] at ih ⊢ <;> exact ih
      · cases retained : keep entry.2 <;> simp [workerEvents,selected,retained] at ih ⊢ <;> exact ih

theorem integerEvents_filter (current stop : Int) (stride : Nat) (events : Int → List (MemoryWrite α))
    (keep : MemoryWrite α → Bool) :
    (integerEvents current stop stride events).filter keep =
      integerEvents current stop stride (fun i => (events i).filter keep) := by
  by_cases zero : stride = 0
  · conv_lhs => rw [integerEvents,ite_eq_left zero]
    conv_rhs => rw [integerEvents,ite_eq_left zero]
    rfl
  · by_cases active : current < stop
    · conv_lhs => rw [integerEvents,ite_eq_right zero,ite_eq_left active]
      conv_rhs => rw [integerEvents,ite_eq_right zero,ite_eq_left active]
      rw [List.filter_append,integerEvents_filter (current+stride) stop stride events keep]
    · conv_lhs => rw [integerEvents,ite_eq_right zero,ite_eq_right active]
      conv_rhs => rw [integerEvents,ite_eq_right zero,ite_eq_right active]
      rfl
termination_by (stop-current).toNat
decreasing_by omega

#axiomsClean MemoryWrite.lanes_stores
#axiomsClean workerEvents_filter
#axiomsClean mem_workerEvents
#axiomsClean integerEvents_filter
end Interleaved
end
end VeriTile.Triton.FP.Structural
