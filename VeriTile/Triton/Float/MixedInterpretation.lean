import VeriTile.Triton.Float.MinimumExpression
import VeriTile.Triton.Float.ReductionInterpretation
import VeriTile.Triton.Float.AtomicExpression

/-! Compose scalar, full-tile dot, sum, maximum, minimum and ordered atomic
interpretations. Each label retains its own primitive and exact arguments;
unhandled symbols still use the supplied fallback. No kernel result is assumed. -/
namespace VeriTile.Triton.FP.Equational
open Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Atom Value : Type} [Inhabited Value]

def mixedSymbolic : Algebra (Term Atom) :=
  atomicExpressionBackend (withMinimumCalls (withFusedCalls (algebra seededSchedules)))

def mixedCalls (M : Algebra Value) (D : DotAccumulator Value)
    (fallback : Symbol → List Value → Value) : Symbol → List Value → Value :=
  primitiveCalls M D (reductionCalls M (minimumCalls M (atomicCalls M fallback)))

theorem mixedCalls_reduction (M : Algebra Value) (D : DotAccumulator Value)
    (fallback : Symbol → List Value → Value) :
    reductionCalls M (mixedCalls M D fallback) = mixedCalls M D fallback := by
  funext symbol args
  cases symbol <;> rfl

theorem mixed_maximum_evaluates (M : Algebra Value) (D : DotAccumulator Value)
    (fallback : Symbol → List Value → Value) (leaf : Atom → Value)
    (precision : Option ComputeDType) (shape : TileShape) (dimension : Fin shape.length) (keepDims : Bool)
    (values : Values (Term Atom) .real shape) (index : TileIndex (TileShape.reduceShape shape dimension keepDims)) :
    (mixedSymbolic.reduceMax precision dimension keepDims values index).evaluate leaf (mixedCalls M D fallback) =
      M.reduceMax precision dimension keepDims (fun i => (values i).evaluate leaf (mixedCalls M D fallback)) index := by
  change ((algebra seededSchedules).reduceMax precision dimension keepDims values index).evaluate leaf (mixedCalls M D fallback) = _
  have result := maximum_evaluates M (mixedCalls M D fallback) leaf seededSchedules precision shape dimension keepDims values index
  simpa only [mixedCalls_reduction] using result

/-- Complete sums compose with the same scalar, cast, dot and atomic
interpretations; the explicit tree backend is still available independently. -/
theorem mixed_sum_evaluates (M : Algebra Value) (D : DotAccumulator Value)
    (fallback : Symbol → List Value → Value) (leaf : Atom → Value)
    (base : Algebra (Term Atom)) (precision : Option ComputeDType)
    (shape : TileShape) (dimension : Fin shape.length) (keepDims : Bool)
    (values : Values (Term Atom) .real shape) (index : TileIndex (TileShape.reduceShape shape dimension keepDims)) :
    ((withSumCalls base).reduceSum precision dimension keepDims values index).evaluate leaf (mixedCalls M D fallback) =
      M.reduceSum precision dimension keepDims (fun i => (values i).evaluate leaf (mixedCalls M D fallback)) index := by
  have result := sum_evaluates M (mixedCalls M D fallback) leaf base precision shape dimension keepDims values index
  simpa only [mixedCalls_reduction] using result

theorem mixed_minimum_evaluates (M : Algebra Value) (D : DotAccumulator Value)
    (fallback : Symbol → List Value → Value) (leaf : Atom → Value)
    (precision : Option ComputeDType) (dtype : FloatDType) (a b : Term Atom)
    (minimum : Value → Value → Value) (available : M.minimum precision dtype = some minimum) :
    (Term.app (.minimum precision dtype) [a,b]).evaluate leaf (mixedCalls M D fallback) =
      minimum (a.evaluate leaf (mixedCalls M D fallback)) (b.evaluate leaf (mixedCalls M D fallback)) := by
  simp only [Term.evaluate,List.map_cons,List.map_nil,mixedCalls,primitiveCalls,dotCalls,scalarCalls,
    reductionCalls,minimumCalls,available]

theorem mixed_atomic_evaluates (M : Algebra Value) (D : DotAccumulator Value)
    (fallback : Symbol → List Value → Value) (leaf : Atom → Value)
    (operation : RMWOp) (dtype : FloatDType) (previous incoming : Term Atom)
    (combine : Value → Value → Value) (available : M.atomicReduce operation dtype = some combine) :
    (Term.app (.atomicReduce operation dtype) [previous,incoming]).evaluate leaf (mixedCalls M D fallback) =
      combine (previous.evaluate leaf (mixedCalls M D fallback)) (incoming.evaluate leaf (mixedCalls M D fallback)) := by
  simp only [Term.evaluate,List.map_cons,List.map_nil,mixedCalls,primitiveCalls,dotCalls,scalarCalls,
    reductionCalls,minimumCalls,atomicCalls,available]

#axiomsClean mixed_sum_evaluates
#axiomsClean mixedCalls_reduction
#axiomsClean mixed_maximum_evaluates
#axiomsClean mixed_minimum_evaluates
#axiomsClean mixed_atomic_evaluates
end
end VeriTile.Triton.FP.Equational
