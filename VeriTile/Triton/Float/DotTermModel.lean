import VeriTile.Triton.Float.TermModel
import VeriTile.Triton.Float.DotAccumulator

/-! Reify a complete typed tile contraction as a primitive numerical call.
The symbol retains tile dimensions, formats, accumulator precision, options and
output position. Operands retain every lane in a fixed order, including masked
padding. This gives no reassociation, padding-elimination or hardware law. -/
namespace VeriTile.Triton.FP.Equational
open Structural

variable {α : Type}

def dotArguments (left right out : FloatDType) {batch : TileShape} {m k n : Nat}
    (a : Values (Term α) left.toTileDType (batch ++ [m,k]))
    (b : Values (Term α) right.toTileDType (batch ++ [k,n]))
    (acc : Values (Term α) out.toTileDType (batch ++ [m,n])) : List (Term α) :=
  (TileShape.allIndices (batch ++ [m,k])).map (fun i => toFloat left (a i)) ++
  (TileShape.allIndices (batch ++ [k,n])).map (fun i => toFloat right (b i)) ++
  (TileShape.allIndices (batch ++ [m,n])).map (fun i => toFloat out (acc i))

def dotAccumulator : DotAccumulator (Term α) := fun precision left right out options
    {batch} {m k n} a b acc i =>
  ofFloat out (.app (.dotAcc precision left right out options batch m k n i)
    (dotArguments left right out a b acc))

/-- Fused calls are represented separately from multiply and add, so reifying a
source never silently contracts them. -/
def withFusedCalls (M : Algebra (Term α)) : Algebra (Term α) :=
  { M with
    fma := fun precision => some fun a b c => .app (.fma precision) [a,b,c]
    fmaTyped := fun dtype => some fun a b c => .app (.fmaTyped dtype) [a,b,c] }

theorem dotAccumulator_value (precision : Option ComputeDType) (left right out : FloatDType)
    (options : DotOptions) {batch : TileShape} {m k n : Nat}
    (a : Values (Term α) left.toTileDType (batch ++ [m,k]))
    (b : Values (Term α) right.toTileDType (batch ++ [k,n]))
    (acc : Values (Term α) out.toTileDType (batch ++ [m,n]))
    (i : TileIndex (batch ++ [m,n])) :
    toFloat out (dotAccumulator precision left right out options a b acc i) =
      .app (.dotAcc precision left right out options batch m k n i)
        (dotArguments left right out a b acc) := by
  cases out <;> rfl

#axiomsClean dotAccumulator_value
end VeriTile.Triton.FP.Equational
