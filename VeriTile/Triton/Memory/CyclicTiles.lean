import VeriTile.Triton.Memory.TriangularTiles

/-! Cyclic ownership for persistent workers. These are index and ordering
facts only; they assert no independence of floating-point atomic updates. -/
namespace VeriTile.Triton.CyclicTiles

def tile (workers worker iteration : Nat) : Nat := iteration*workers+worker

def owner (workers index : Nat) : Nat := index % workers

def iteration (workers index : Nat) : Nat := index / workers

theorem covered (workers index : Nat) : tile workers (owner workers index) (iteration workers index) = index := by
  simpa [tile,owner,iteration,Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div index workers

theorem owner_bound {workers : Nat} (positive : 0 < workers) (index : Nat) : owner workers index < workers :=
  Nat.mod_lt index positive

theorem tile_owner {workers worker : Nat} (inside : worker < workers) (step : Nat) :
    owner workers (tile workers worker step) = worker := by
  simp [tile,owner,Nat.add_mod,Nat.mod_eq_of_lt inside]

theorem tile_iteration {workers worker : Nat} (inside : worker < workers) (step : Nat) :
    iteration workers (tile workers worker step) = step :=
  TriangularTiles.lane_block (Nat.zero_lt_of_lt inside) inside step

theorem unique {workers firstWorker secondWorker firstStep secondStep : Nat}
    (firstInside : firstWorker < workers) (secondInside : secondWorker < workers)
    (same : tile workers firstWorker firstStep = tile workers secondWorker secondStep) :
    firstWorker = secondWorker ∧ firstStep = secondStep := by
  have owners := congrArg (owner workers) same
  have steps := congrArg (iteration workers) same
  rw [tile_owner firstInside,tile_owner secondInside] at owners
  rw [tile_iteration firstInside,tile_iteration secondInside] at steps
  exact ⟨owners,steps⟩

theorem next (workers worker step : Nat) : tile workers worker (step+1) = tile workers worker step + workers := by
  simp [tile,Nat.add_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem strictly_increasing {workers : Nat} (positive : 0 < workers) (worker : Nat) :
    ∀ first second, first < second → tile workers worker first < tile workers worker second := by
  intro first second before
  exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right before positive) worker

theorem row_column_bounds {rows columns index : Nat} (positive : 0 < columns) (inside : index < rows*columns) :
    index/columns < rows ∧ index%columns < columns := by
  exact ⟨(Nat.div_lt_iff_lt_mul positive).mpr inside,Nat.mod_lt index positive⟩

theorem row_column_reconstruct (columns index : Nat) : (index/columns)*columns+index%columns = index := by
  simpa [Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div index columns

#axiomsClean covered
#axiomsClean owner_bound
#axiomsClean tile_owner
#axiomsClean tile_iteration
#axiomsClean unique
#axiomsClean next
#axiomsClean strictly_increasing
#axiomsClean row_column_bounds
#axiomsClean row_column_reconstruct
end VeriTile.Triton.CyclicTiles
