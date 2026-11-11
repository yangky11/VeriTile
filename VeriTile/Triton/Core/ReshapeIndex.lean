import VeriTile.Triton.Core.Reshape
import VeriTile.Meta.StatementAudit

/-! Exact row-major coordinates for arbitrary-rank reshapes. These lemmas keep
all lanes and avoid enumerating a concrete tile while proving a source layout. -/
namespace VeriTile.Triton.TileShape

private theorem flatMap_uniform_length {α β : Type} (xs : List α) (f : α → List β) (width : Nat)
    (lengths : ∀ x ∈ xs, (f x).length = width) : (xs.flatMap f).length = xs.length*width := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    rw [lengths x (by simp),ih (fun y hy => lengths y (by simp [hy]))]
    omega

private theorem flatMap_uniform_get {α β : Type} (xs : List α) (f : α → List β) (width : Nat)
    (lengths : ∀ x ∈ xs, (f x).length = width) (i : Fin xs.length) (j : Fin width) :
    (xs.flatMap f)[i.val*width+j.val]'(by
      rw [flatMap_uniform_length xs f width lengths]
      exact lt_of_lt_of_le (Nat.add_lt_add_left j.isLt _) (by
        simpa only [Nat.add_mul,Nat.one_mul,Nat.succ_eq_add_one] using Nat.mul_le_mul_right width i.isLt)) =
    (f xs[i.val])[j.val]'(by rw [lengths _ (List.getElem_mem _)]; exact j.isLt) := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
    have headLength := lengths x (by simp)
    have tailLengths : ∀ y ∈ xs, (f y).length = width := fun y hy => lengths y (by simp [hy])
    cases i using Fin.cases with
    | zero =>
      simp only [Fin.val_zero,Nat.zero_mul,Nat.zero_add,List.flatMap_cons,List.getElem_cons_zero]
      exact List.getElem_append_left (by rw [headLength]; exact j.isLt)
    | succ i =>
      simp only [Fin.val_succ,List.flatMap_cons,List.getElem_cons_succ]
      rw [List.getElem_append_right (by rw [headLength,Nat.add_mul,Nat.one_mul]; omega)]
      have offset : (i.val+1)*width+j.val-(f x).length = i.val*width+j.val := by
        rw [headLength,Nat.add_mul,Nat.one_mul]
        omega
      simp only [offset]
      exact ih tailLengths i

theorem allIndices_get_linear (shape : TileShape) (i : TileIndex shape) :
    (allIndices shape)[linearIndex shape i]'(by rw [length_allIndices]; exact linearIndex_lt shape i) = i := by
  induction shape with
  | nil => cases i; rfl
  | cons n rest ih =>
    simp only [allIndices,linearIndex]
    rw [flatMap_uniform_get (List.finRange n) (fun head => (allIndices rest).map (Prod.mk head))
      (product rest) (by intro head _; simp) (⟨i.1.val,by simp⟩)
      (⟨linearIndex rest i.2,linearIndex_lt rest i.2⟩)]
    simp only [List.getElem_finRange,List.getElem_map,ih]
    apply Prod.ext
    · apply Fin.ext; rfl
    · rfl

theorem linearIndex_injective (shape : TileShape) : Function.Injective (linearIndex shape) := by
  intro a b equal
  have one := allIndices_get_linear shape a
  have two := allIndices_get_linear shape b
  have indexEqual : (⟨linearIndex shape a, by simpa using linearIndex_lt shape a⟩ :
      Fin (allIndices shape).length) = ⟨linearIndex shape b, by simpa using linearIndex_lt shape b⟩ :=
    Fin.ext equal
  exact one.symm.trans ((congrArg (List.get (allIndices shape)) indexEqual).trans two)

theorem linearIndex_allIndices (shape : TileShape) (i : Fin (product shape)) :
    linearIndex shape ((allIndices shape)[i.val]'(by simp)) = i.val := by
  exact (allIndices_nodup shape).getElem_inj_iff.mp (allIndices_get_linear shape _)

theorem reshapeIndex_linear {input output : TileShape} (same : product input = product output)
    (i : TileIndex output) : linearIndex input (reshapeIndex same i) = linearIndex output i := by
  exact linearIndex_allIndices input ⟨linearIndex output i,by rw [same]; exact linearIndex_lt output i⟩

theorem reshapeIndex_of_linear {input output : TileShape} (same : product input = product output)
    (i : TileIndex output) (j : TileIndex input) (equal : linearIndex input j = linearIndex output i) :
    reshapeIndex same i = j :=
  linearIndex_injective input ((reshapeIndex_linear same i).trans equal.symm)

theorem reshapeIndex_roundtrip {input output : TileShape} (same : product input = product output)
    (i : TileIndex input) : reshapeIndex same (reshapeIndex same.symm i) = i := by
  apply reshapeIndex_of_linear
  exact (reshapeIndex_linear same.symm i).symm

/-- Splitting a matrix's columns into groups retains the whole accumulator:
group `g`, lane `j` selects column `g * width + j`. No tile-size enumeration
or assumption about the values (including padded lanes) is involved. -/
theorem reshapeIndex_groupColumns {rows groups width : Nat}
    (i : Fin rows) (g : Fin groups) (j : Fin width) :
    reshapeIndex (input := [rows,groups*width]) (output := [rows,groups,width])
      (by simp [product]) (i,g,j,PUnit.unit) =
      (i,⟨g.val*width+j.val,by
        calc
          _ < g.val*width+width := Nat.add_lt_add_left j.isLt _
          _ = (g.val+1)*width := (Nat.succ_mul _ _).symm
          _ ≤ groups*width := Nat.mul_le_mul_right width g.isLt⟩,PUnit.unit) := by
  apply reshapeIndex_of_linear
  simp [linearIndex,product]

#axiomsClean allIndices_get_linear
#axiomsClean linearIndex_injective
#axiomsClean linearIndex_allIndices
#axiomsClean reshapeIndex_linear
#axiomsClean reshapeIndex_of_linear
#axiomsClean reshapeIndex_roundtrip
#axiomsClean reshapeIndex_groupColumns
end VeriTile.Triton.TileShape
