import VeriTile.Triton.Float.DotInterpretation
import VeriTile.Meta.StatementAudit

/-! Interpretation of complete source sum and maximum reduction calls. Precision,
shape, axis, keep-dimension flag, all operand lanes and the output index are
retained. No associativity, row independence or scalar maximum law is assumed. -/
namespace VeriTile.Triton.FP.Equational
open Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Opt into complete sum calls without changing the explicit addition-tree
semantics of `algebra plans`. Every lane and the full reduction descriptor are
retained; no associativity, padding or row-locality law is introduced. -/
def withSumCalls {α : Type} (base : Algebra (Term α)) : Algebra (Term α) :=
  { base with
    reduceSum := fun precision {shape} axis keepDims values index =>
      .app (.reduceSum precision shape axis keepDims index) ((TileShape.allIndices shape).map values) }

/-- Reconstruct the exact typed tile before invoking one numerical primitive.
Other symbols keep their independently supplied interpretations. -/
def reductionCalls {α : Type} [Inhabited α] (M : Algebra α)
    (fallback : Symbol → List α → α) : Symbol → List α → α
  | .reduceSum precision shape axis keepDims index,words =>
      M.reduceSum precision axis keepDims (tileFromWords .real shape words) index
  | .reduceMax precision shape axis keepDims index,words =>
      M.reduceMax precision axis keepDims (tileFromWords .real shape words) index
  | symbol,words => fallback symbol words

theorem maximum_expression_evaluates {α β : Type} [Inhabited β] (M : Algebra β)
    (fallback : Symbol → List β → β) (leaf : α → β) (precision : Option ComputeDType)
    (shape : TileShape) (axis : Fin shape.length) (keepDims : Bool)
    (values : Values (Term α) .real shape) (index : TileIndex (TileShape.reduceShape shape axis keepDims)) :
    (Term.app (.reduceMax precision shape axis keepDims index)
      ((TileShape.allIndices shape).map values)).evaluate leaf (reductionCalls M fallback) =
      M.reduceMax precision axis keepDims
        (fun i => (values i).evaluate leaf (reductionCalls M fallback)) index := by
  simp only [Term.evaluate,reductionCalls,List.map_map]
  have restored := tileFromWords_words .real
    (fun i => (values i).evaluate leaf (reductionCalls M fallback) : Values β .real shape)
  simpa only [tileWords,toFloat,Function.comp_def,id_eq] using congrArg (fun tile => M.reduceMax precision axis keepDims tile index) restored

theorem maximum_evaluates {α β : Type} [Inhabited β] (M : Algebra β)
    (fallback : Symbol → List β → β) (leaf : α → β) (plans : Schedules)
    (precision : Option ComputeDType) (shape : TileShape) (axis : Fin shape.length) (keepDims : Bool)
    (values : Values (Term α) .real shape) (index : TileIndex (TileShape.reduceShape shape axis keepDims)) :
    ((algebra plans).reduceMax precision axis keepDims values index).evaluate leaf (reductionCalls M fallback) =
      M.reduceMax precision axis keepDims
        (fun i => (values i).evaluate leaf (reductionCalls M fallback)) index :=
  maximum_expression_evaluates M fallback leaf precision shape axis keepDims values index

theorem sum_expression_evaluates {α β : Type} [Inhabited β] (M : Algebra β)
    (fallback : Symbol → List β → β) (leaf : α → β) (precision : Option ComputeDType)
    (shape : TileShape) (axis : Fin shape.length) (keepDims : Bool)
    (values : Values (Term α) .real shape) (index : TileIndex (TileShape.reduceShape shape axis keepDims)) :
    (Term.app (.reduceSum precision shape axis keepDims index)
      ((TileShape.allIndices shape).map values)).evaluate leaf (reductionCalls M fallback) =
      M.reduceSum precision axis keepDims
        (fun i => (values i).evaluate leaf (reductionCalls M fallback)) index := by
  simp only [Term.evaluate,reductionCalls,List.map_map]
  have restored := tileFromWords_words .real
    (fun i => (values i).evaluate leaf (reductionCalls M fallback) : Values β .real shape)
  simpa only [tileWords,toFloat,Function.comp_def,id_eq] using congrArg (fun tile => M.reduceSum precision axis keepDims tile index) restored

theorem sum_evaluates {α β : Type} [Inhabited β] (M : Algebra β)
    (fallback : Symbol → List β → β) (leaf : α → β) (base : Algebra (Term α))
    (precision : Option ComputeDType) (shape : TileShape) (axis : Fin shape.length) (keepDims : Bool)
    (values : Values (Term α) .real shape) (index : TileIndex (TileShape.reduceShape shape axis keepDims)) :
    ((withSumCalls base).reduceSum precision axis keepDims values index).evaluate leaf (reductionCalls M fallback) =
      M.reduceSum precision axis keepDims
        (fun i => (values i).evaluate leaf (reductionCalls M fallback)) index :=
  sum_expression_evaluates M fallback leaf precision shape axis keepDims values index

#axiomsClean sum_expression_evaluates
#axiomsClean sum_evaluates
#axiomsClean maximum_expression_evaluates
#axiomsClean maximum_evaluates
end
end VeriTile.Triton.FP.Equational
