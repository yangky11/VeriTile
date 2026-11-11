import VeriTile.Triton.Float.FmaContraction
import VeriTile.Triton.Float.DotTermModel

open VeriTile.Triton VeriTile.Triton.FP.Equational

-- Two legal contraction choices for the same source expression remain distinct.
example (alpha acc beta residual : Term Nat) :
    contractRoot .left ((alpha.mul32 acc).add (beta.mul32 residual)) =
      some (alpha.fma32 acc (beta.mul32 residual)) := rfl

example (alpha acc beta residual : Term Nat) :
    contractRoot .right ((alpha.mul32 acc).add (beta.mul32 residual)) =
      some (beta.fma32 residual (alpha.mul32 acc)) := rfl

example (a b c : Term Nat) :
    contractRoot .left (.app (.binary (some .fp64) .real .add) [a.mul32 b,c]) = none := rfl

example (a b c : Term Nat) :
    contractRoot .left ((Term.app (.cast (some .fp32) .real .bf16) [a.mul32 b]).add c) = none := rfl

-- FMA is not a word-equivalence rule. This is an executable host counterexample,
-- separate from the structural theorems; it makes no hardware-wide claim.
#eval (do
  let a := Float32.ofBits 0x3f800001
  let b := Float32.ofBits 0x3f7ffffe
  let c := Float32.ofBits 0xbf800000
  let strict := (a*b+c).toBits
  let fused := (a.fma b c).toBits
  unless strict == 0 && fused == 0xa8800000 do
    throw (IO.userError s!"unexpected host FMA counterexample: {strict}, {fused}")
  : IO Unit)

example : dotArguments .bf16 .bf16 .real (batch := []) (m := 1) (k := 2) (n := 1)
    (fun i => .leaf (10+i.2.1.val)) (fun i => .leaf (20+i.1.val)) (fun _ => .leaf 30) =
    [.leaf 10,.leaf 11,.leaf 20,.leaf 21,.leaf 30] := by rfl

private def stored (value : Term Nat) : Term Nat :=
  .app (.cast none .bf16 .bf16) [.app (.cast (some .fp32) .real .bf16) [value]]

example (a b c : Term Nat) :
    contractAll [{path := [0,0], side := .left}] (stored ((a.mul32 b).add c)) =
      some (stored (a.fma32 b c)) := rfl

example (a b c : Term Nat) :
    contractAt .left [1] (stored ((a.mul32 b).add c)) = none := rfl

-- Subtraction is opt-in: old witnesses cannot silently acquire signed FMA.
example (a b c : Term Nat) :
    contractRoot .right (c.sub32 (a.mul32 b)) = none := rfl

example (a b c : Term Nat) :
    contractRoot .left ((a.mul32 b).sub32 c) .subtract =
      some (a.fma32 b c.neg32) := rfl

example (a b c : Term Nat) :
    contractRoot .right (c.sub32 (a.mul32 b)) .subtract =
      some (a.neg32.fma32 b c) := rfl

example (a b c : Term Nat) :
    contractRoot .right (c.add (a.mul32 b)) .subtract = none := rfl

example (a b c : Term Nat) :
    contractRoot .right (c.sub32 (.app (.cast (some .fp32) .real .bf16) [a.mul32 b]))
      .subtract = none := rfl

example (a b c : Term Nat) :
    contractRoot .right (.app (.binary (some .fp64) .real .sub) [c,a.mul32 b])
      .subtract = none := rfl

example (a b c : Term Nat) :
    contractRoot .right (c.sub32 (.app (.binary (some .fp32) .bf16 .mul) [a,b]))
      .subtract = none := rfl

example (a b c : Term Nat) :
    contractAll [{path := [0,0], side := .right, combine := .subtract}]
      (stored (c.sub32 (a.mul32 b))) = some (stored (a.neg32.fma32 b c)) := rfl

example (a b c : Term Nat) :
    FmaContraction (stored (c.sub32 (a.mul32 b))) (stored (a.neg32.fma32 b c)) :=
  contractAll_sound [{path := [0,0], side := .right, combine := .subtract}] _ _ rfl

-- Different rounding is intentional, including for subtraction.
#eval (do
  let a := Float32.ofBits 0x3f800001
  let b := Float32.ofBits 0x3f7ffffe
  let c := Float32.ofBits 0x3f800000
  let strict := (c-a*b).toBits
  let fused := ((-a).fma b c).toBits
  unless strict == 0 && fused == 0x28800000 do
    throw (IO.userError s!"unexpected host subtract-FMA counterexample: {strict}, {fused}")
  : IO Unit)
