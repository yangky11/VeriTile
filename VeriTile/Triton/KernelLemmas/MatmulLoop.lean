import VeriTile.Triton.KernelLemmas.Matmul
import VeriTile.Triton.KernelLemmas.LoopInvariant

/-! A block-dot accumulation invariant independent of tile dimensions, register
representation and memory layout. Clients supply the source body step, including
its execution and auxiliary invariant; this theorem supplies the K induction. -/
namespace VeriTile.Triton
noncomputable section

/-- Accumulating one finite dot per iteration yields the full contraction.
`P` carries any memory, offset, mask or register facts the next step needs. -/
theorem forLoop_gemmSum {α : Type} {idx : RegName} {n block : Nat}
    {body : List Stmt} {initial : BlockState} (P : Nat → BlockState → Prop)
    (read : BlockState → α → ℝ) (a b : α → Nat → ℝ)
    (hinit : P 0 initial) (hzero : ∀ lane, read initial lane = 0)
    (hstep : ∀ i s, i < n → P i s →
      (∀ lane, read s lane = gemmSum (a lane) (b lane) (i * block)) →
      ∃ next, stepStmts body (s.setReg idx .nat [] (Tile.scalar i)) = some next ∧
        P (i + 1) next ∧
        ∀ lane, read next lane = read s lane +
          ∑ k : Fin block, a lane (i * block + k.val) * b lane (i * block + k.val)) :
    ∃ final, stepStmt (.forLoop idx n body) initial = some final ∧ P n final ∧
      ∀ lane, read final lane = gemmSum (a lane) (b lane) (n * block) := by
  apply forLoop_inv (P := fun i s => P i s ∧
    ∀ lane, read s lane = gemmSum (a lane) (b lane) (i * block))
  · exact ⟨hinit, by simpa using hzero⟩
  · intro i s hi hs
    obtain ⟨next, executes, invariant, update⟩ := hstep i s hi hs.1 hs.2
    refine ⟨next, executes, invariant, ?_⟩
    intro lane
    rw [update, hs.2, gemmSum_blockSucc]

end
end VeriTile.Triton
