import VeriTile.Triton.Float.Structural
import VeriTile.Meta.StatementAudit

/-! Total typed dot-accumulation policies for source execution proofs. This is
one numerical primitive, not an opaque kernel. Every operand channel, compute
precision, option and tile layout remains an argument. Supplying a policy does
not assert hardware support or an expansion into scalar arithmetic. -/
namespace VeriTile.Triton.FP.Structural

abbrev DotAccumulator (α : Type) :=
  Option ComputeDType → (left right out : FloatDType) → DotOptions →
    {batch : TileShape} → {m k n : Nat} →
    Values α left.toTileDType (batch ++ [m,k]) →
    Values α right.toTileDType (batch ++ [k,n]) →
    Values α out.toTileDType (batch ++ [m,n]) →
    Values α out.toTileDType (batch ++ [m,n])

def Algebra.withDotAccumulator {α : Type} (M : Algebra α) (D : DotAccumulator α) : Algebra α :=
  { M with
    dotAcc := fun precision left right out options {_} {_} {_} {_} a b acc =>
      some (D precision left right out options a b acc) }

@[simp] theorem Algebra.withDotAccumulator_apply {α : Type} (M : Algebra α) (D : DotAccumulator α)
    (precision : Option ComputeDType) (left right out : FloatDType) (options : DotOptions)
    {batch : TileShape} {m k n : Nat}
    (a : Values α left.toTileDType (batch ++ [m,k]))
    (b : Values α right.toTileDType (batch ++ [k,n]))
    (acc : Values α out.toTileDType (batch ++ [m,n])) :
    (M.withDotAccumulator D).dotAcc precision left right out options a b acc =
      some (D precision left right out options a b acc) := rfl

#axiomsClean Algebra.withDotAccumulator_apply
#axiomsClean evalComputeOp_const_fp32
#axiomsClean evalComputeOp_full
end VeriTile.Triton.FP.Structural
