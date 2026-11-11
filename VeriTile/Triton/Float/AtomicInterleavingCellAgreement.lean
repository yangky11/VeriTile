import VeriTile.Triton.Float.AtomicInterleavingControlMemory
import VeriTile.Triton.Float.AtomicInterleavingDependencies
import VeriTile.Triton.Float.SourceCellAgreement

/-! Corresponding worker ticks preserve agreement on arbitrary owned cells.
This theorem does not require other memory cells to agree. -/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

theorem tick_cells_agree (M : Algebra α) (regions : RegionName → Prop) (cells : RegionName → Nat → Prop)
    (code : List Command) (dependent : pendingDependencies regions code)
    (first second : State α) (final other : Local α)
    (same : first.AgreesOn regions second) (equalCells : first.CellsAgree cells second)
    (one : (Local.mk code first).tick M first.mem = some final)
    (two : (Local.mk code second).tick M second.mem = some other) :
    final.state.CellsAgree cells other.state := by
  by_cases control : leafHead code = false
  · have firstMemory := Local.tick_control_memory M _ _ first.mem control one
    have secondMemory := Local.tick_control_memory M _ _ second.mem control two
    intro region offset owned
    rw [firstMemory,secondMemory]
    exact equalCells region offset owned
  · cases code with
    | nil => simp [leafHead] at control
    | cons command rest =>
      cases command with
      | counted | natural | integer => simp [leafHead] at control
      | source statement =>
        have supported : leafSupported statement = true := Bool.eq_true_of_not_eq_false control
        have dependency := (pendingDependencies_cons regions (.source statement) rest).mp dependent |>.1
        cases firstRun : step M statement first with
        | none => simp [Local.tick,supported,firstRun] at one
        | some firstFinal =>
          cases secondRun : step M statement second with
          | none => simp [Local.tick,supported,secondRun] at two
          | some secondFinal =>
            simp [Local.tick,supported,firstRun] at one
            simp [Local.tick,supported,secondRun] at two
            subst final other
            exact readDependencies_leaf_cells_agree M regions cells statement dependency supported
              first second firstFinal secondFinal same equalCells firstRun secondRun

#axiomsClean tick_cells_agree
end
end VeriTile.Triton.FP.Structural.Interleaved
