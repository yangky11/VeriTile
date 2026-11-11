import VeriTile.Triton.Float.Structural
import VeriTile.Triton.Core.ReshapeIndex
import VeriTile.Meta.StatementAudit

/-! Shape transformations preserve arbitrary typed values and precision contexts.
These statements do not require arithmetic identities or discard padded lanes. -/
namespace VeriTile.Triton.FP.Structural

theorem evalOp_reshape_of_value {α : Type} [Inhabited α] (M : Algebra α)
    (precision : Option ComputeDType) (s : State α) (e : Op dtype input)
    (v : Values α dtype input) (evaluated : evalOp M precision e s = some v)
    (same : TileShape.product input = TileShape.product output) :
    evalOp M precision (.reshape output e) s =
      some (fun i => v (TileShape.reshapeIndex same i)) := by
  change (evalOp M precision e s).bind (fun value =>
    if h : TileShape.product input = TileShape.product output then
      some (fun i => value (TileShape.reshapeIndex h i)) else none) = _
  rw [evaluated]
  simp only [Option.bind_some,dite_eq_left same]

theorem evalOp_reshape_roundtrip {α : Type} [Inhabited α] (M : Algebra α)
    (precision : Option ComputeDType) (s : State α) (e : Op dtype input)
    (v : Values α dtype input) (evaluated : evalOp M precision e s = some v)
    (same : TileShape.product input = TileShape.product output) :
    evalOp M precision (.reshape input (.reshape output e)) s = some v := by
  rw [evalOp_reshape_of_value M precision s _ _
    (evalOp_reshape_of_value M precision s e v evaluated same) same.symm]
  congr 1
  funext i
  rw [TileShape.reshapeIndex_roundtrip]

/-- A reshape followed by a last-two-axis permutation and split extracts a
half-column tile from the original accumulator, for every dtype and backend. -/
theorem evalOp_splitColumns {α : Type} [Inhabited α] (M : Algebra α)
    (precision : Option ComputeDType) (s : State α) (e : Op dtype [rows,2*width])
    (v : Values α dtype [rows,2*width]) (evaluated : evalOp M precision e s = some v)
    (side : Fin 2) :
    evalOp M precision (.split (shape := [rows,width]) side
      (.remap [rows,width,2] (fun i => (i.1,i.2.2.1,i.2.1,PUnit.unit))
        (.reshape [rows,2,width] e))) s =
      some (fun i => v (i.1,⟨side.val*width+i.2.1.val,by
        calc
          _ < side.val*width+width := Nat.add_lt_add_left i.2.1.isLt _
          _ = (side.val+1)*width := (Nat.succ_mul _ _).symm
          _ ≤ 2*width := Nat.mul_le_mul_right width side.isLt⟩,PUnit.unit)) := by
  have same : TileShape.product [rows,2*width] = TileShape.product [rows,2,width] := by
    simp [TileShape.product]
  change ((evalOp M precision (.reshape [rows,2,width] e) s).bind
    (fun value => some (fun i : TileIndex [rows,width,2] =>
      value (i.1,i.2.2.1,i.2.1,PUnit.unit)))).bind
    (fun value => some (fun i => value (TileShape.appendAxisIndex [rows,width] i side))) = _
  rw [evalOp_reshape_of_value M precision s e v evaluated same]
  simp only [Option.bind_some]
  congr 1
  funext i
  change v (TileShape.reshapeIndex same (i.1,side,i.2.1,PUnit.unit)) = _
  rw [TileShape.reshapeIndex_groupColumns]

#axiomsClean evalOp_reshape_of_value
#axiomsClean evalOp_reshape_roundtrip
#axiomsClean evalOp_splitColumns
end VeriTile.Triton.FP.Structural
