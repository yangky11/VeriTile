import VeriTile.Triton.Launch.Composition

/-! A singleton launch has the memory of its one source execution. This is a
property of the existing ordinary-grid relation; it does not replace that
relation with a serial interpretation for non-singleton grids. -/
namespace VeriTile.Triton
namespace Kernel

/-- Lift the one program's successful source execution into a whole ordinary
grid. No additional frame assumption is necessary: one writer cannot overlap
another writer, and every final cell comes from that one execution. -/
theorem ordinary_singleton {kernel : Kernel} {grid : Grid}
    [Subsingleton (GridIndex grid)] (index : GridIndex grid) (initial final : BlockState)
    (ran : exec kernel (initial.withGridIndex index) = some final) :
    ∃ merged, Nonempty (GridLaunchedOrdinary kernel grid initial merged) ∧
      merged.mem = final.mem := by
  let frames : GridFrames kernel grid initial := fun other => {
    final := final
    writes := fun _ => True
    h_exec := by simpa only [Subsingleton.elim other index] using ran
    h_writeWithin := by intro _ _ outside; exact False.elim (outside trivial)
  }
  have disjoint : GridWritesDisjoint frames := by
    intro left right different
    exact False.elim (different (Subsingleton.elim _ _))
  refine ⟨mergeFrames grid initial frames, ⟨⟨frames, disjoint, rfl⟩⟩, ?_⟩
  funext region offset
  exact mergeFrames_mem_written disjoint index region offset trivial

end Kernel
end VeriTile.Triton
