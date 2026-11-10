import VeriTile.Triton.Float.DotTermModel

/-! Interpret reified full-tile dot calls through the same typed numerical
primitive. Enumeration and reconstruction preserve every operand and accumulator
lane. No scalar expansion, reassociation or hardware equation is assumed. -/
namespace VeriTile.Triton.FP.Equational
open Structural
noncomputable section
variable {α β : Type}

theorem toFloat_ofFloat (dtype : FloatDType) (value : α) :
    toFloat dtype (ofFloat dtype value) = value := by cases dtype <;> rfl

theorem ofFloat_toFloat (dtype : FloatDType) (value : Structural.Value α dtype.toTileDType) :
    ofFloat dtype (toFloat dtype value) = value := by cases dtype <;> rfl

def tileWords (dtype : FloatDType) {shape : TileShape} (values : Values α dtype.toTileDType shape) : List α :=
  (TileShape.allIndices shape).map fun i => toFloat dtype (values i)

/-- Malformed argument lists have a total default interpretation. The roundtrip
theorems below establish that reified calls never use that default. -/
def tileFromWords [Inhabited α] (dtype : FloatDType) (shape : TileShape) (words : List α) :
    Values α dtype.toTileDType shape := by
  classical
  exact fun i => ofFloat dtype (words[(TileShape.allIndices shape).idxOf i]?.getD default)

theorem tileFromWords_words [Inhabited α] (dtype : FloatDType) {shape : TileShape}
    (values : Values α dtype.toTileDType shape) :
    tileFromWords dtype shape (tileWords dtype values) = values := by
  classical
  funext i
  have inside := List.idxOf_lt_length_of_mem (TileShape.mem_allIndices shape i)
  simp only [tileFromWords,tileWords,List.getElem?_map,List.getElem?_eq_getElem inside,
    List.getElem_idxOf,Option.map_some,Option.getD_some,ofFloat_toFloat]

def interpretDot [Inhabited α] (D : DotAccumulator α) (precision : Option ComputeDType)
    (left right out : FloatDType) (options : DotOptions) (batch : TileShape) (m k n : Nat)
    (index : TileIndex (batch ++ [m,n])) (words : List α) : α :=
  let leftCount := (TileShape.allIndices (batch ++ [m,k])).length
  let rightCount := (TileShape.allIndices (batch ++ [k,n])).length
  toFloat out (D precision left right out options
    (tileFromWords left (batch ++ [m,k]) (words.take leftCount))
    (tileFromWords right (batch ++ [k,n]) ((words.drop leftCount).take rightCount))
    (tileFromWords out (batch ++ [m,n]) (words.drop (leftCount+rightCount))) index)

theorem interpretDot_words [Inhabited α] (D : DotAccumulator α) (precision : Option ComputeDType)
    (left right out : FloatDType) (options : DotOptions) {batch : TileShape} {m k n : Nat}
    (a : Values α left.toTileDType (batch ++ [m,k]))
    (b : Values α right.toTileDType (batch ++ [k,n]))
    (acc : Values α out.toTileDType (batch ++ [m,n])) (index : TileIndex (batch ++ [m,n])) :
    interpretDot D precision left right out options batch m k n index
      (tileWords left a ++ tileWords right b ++ tileWords out acc) =
      toFloat out (D precision left right out options a b acc index) := by
  have leftLength : (tileWords left a).length = (TileShape.allIndices (batch ++ [m,k])).length :=
    List.length_map ..
  have rightLength : (tileWords right b).length = (TileShape.allIndices (batch ++ [k,n])).length :=
    List.length_map ..
  simp only [interpretDot,← leftLength,← rightLength,List.append_assoc,List.take_left,List.drop_left,
    ← List.drop_drop,tileFromWords_words]

def dotCalls [Inhabited α] (D : DotAccumulator α) (fallback : Symbol → List α → α) : Symbol → List α → α
  | .dotAcc precision left right out options batch m k n index, words =>
    interpretDot D precision left right out options batch m k n index words
  | op, words => fallback op words

/-- Scalar labels keep their exact precision and format. Unsupported optional
FMA calls and non-scalar labels retain the caller's fallback interpretation. -/
def scalarCalls (M : Algebra α) (fallback : Symbol → List α → α) : Symbol → List α → α
  | .literal precision dtype value, [] => M.literal precision dtype value
  | .negInf, [] => M.negInf
  | .binary precision dtype op, [a,b] => M.binary precision dtype op a b
  | .unary precision op, [a] => M.unary precision op a
  | .cast precision source target, [a] => M.cast precision source target a
  | .fromNat precision value, [] => M.fromNat precision value
  | .fromInt precision value, [] => M.fromInt precision value
  | .fp32Bits bits, [] => M.fp32Bits bits
  | .fp32Load, [a] => M.fp32Load a
  | .fma precision, [a,b,c] => match M.fma precision with
    | some f => f a b c
    | none => fallback (.fma precision) [a,b,c]
  | .fmaTyped dtype, [a,b,c] => match M.fmaTyped dtype with
    | some f => f a b c
    | none => fallback (.fmaTyped dtype) [a,b,c]
  | op, args => fallback op args

def primitiveCalls [Inhabited α] (M : Algebra α) (D : DotAccumulator α)
    (fallback : Symbol → List α → α) : Symbol → List α → α := dotCalls D (scalarCalls M fallback)

def evaluateFloatValues (leaf : α → β) (calls : Symbol → List β → β) (dtype : FloatDType)
    {shape : TileShape} (values : Values (Term α) dtype.toTileDType shape) : Values β dtype.toTileDType shape :=
  fun i => ofFloat dtype ((toFloat dtype (values i)).evaluate leaf calls)

theorem dotArguments_evaluate (leaf : α → β) (calls : Symbol → List β → β)
    (left right out : FloatDType) {batch : TileShape} {m k n : Nat}
    (a : Values (Term α) left.toTileDType (batch ++ [m,k]))
    (b : Values (Term α) right.toTileDType (batch ++ [k,n]))
    (acc : Values (Term α) out.toTileDType (batch ++ [m,n])) :
    (dotArguments left right out a b acc).map (Term.evaluate leaf calls) =
      tileWords left (evaluateFloatValues leaf calls left a) ++
      tileWords right (evaluateFloatValues leaf calls right b) ++
      tileWords out (evaluateFloatValues leaf calls out acc) := by
  simp only [dotArguments,List.map_append,List.map_map,tileWords,evaluateFloatValues,
    toFloat_ofFloat,Function.comp_def]

theorem dotAccumulator_evaluate [Inhabited β] (leaf : α → β) (D : DotAccumulator β)
    (fallback : Symbol → List β → β) (precision : Option ComputeDType)
    (left right out : FloatDType) (options : DotOptions) {batch : TileShape} {m k n : Nat}
    (a : Values (Term α) left.toTileDType (batch ++ [m,k]))
    (b : Values (Term α) right.toTileDType (batch ++ [k,n]))
    (acc : Values (Term α) out.toTileDType (batch ++ [m,n])) (index : TileIndex (batch ++ [m,n])) :
    (toFloat out (dotAccumulator precision left right out options a b acc index)).evaluate
      leaf (dotCalls D fallback) =
      toFloat out (D precision left right out options
        (evaluateFloatValues leaf (dotCalls D fallback) left a)
        (evaluateFloatValues leaf (dotCalls D fallback) right b)
        (evaluateFloatValues leaf (dotCalls D fallback) out acc) index) := by
  rw [dotAccumulator_value]
  simp only [Term.evaluate,dotArguments_evaluate,dotCalls,interpretDot_words]

#axiomsClean toFloat_ofFloat
#axiomsClean ofFloat_toFloat
#axiomsClean tileFromWords_words
#axiomsClean interpretDot_words
#axiomsClean dotArguments_evaluate
#axiomsClean dotAccumulator_evaluate
end
end VeriTile.Triton.FP.Equational
