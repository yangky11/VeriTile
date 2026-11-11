import VeriTile.Triton.Float.MemoryEvaluation

open VeriTile.Triton VeriTile.Triton.FP.Structural VeriTile.Triton.FP.Equational

-- Reification preserves every storage format, arbitrary cells and wrong-tag
-- default reads; no numerical cast or zero law is involved.
example (state : State (BitVec 32)) (calls : Symbol → List (BitVec 32) → BitVec 32)
    (dtype : FloatDType) (region : RegionName) (offset : Nat) :
    (toFloat dtype (((state.map Term.leaf).mem region offset).read dtype.toTileDType)).evaluate id calls =
      toFloat dtype ((state.mem region offset).read dtype.toTileDType) :=
  (reify_memory calls state).words dtype region offset

example (state : State (BitVec 32)) (calls : Symbol → List (BitVec 32) → BitVec 32)
    (pids : Nat → Nat) :
    MemoryEvaluation (Term.evaluate id calls) { state.map Term.leaf with pids := pids }
      { state with pids := pids } :=
  (reify_memory calls state).transport rfl rfl rfl
