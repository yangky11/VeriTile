import VeriTile.Triton.Float.FmaChildren

open VeriTile.Triton VeriTile.Triton.FP.Equational

private def fused (a b c : Term Nat) : ChildContraction Nat :=
  ⟨(a.mul32 b).add c,a.fma32 b c,[{path := [],side := .left}],rfl⟩

private def difference (a b c : Term Nat) : ChildContraction Nat :=
  ⟨c.sub32 (a.mul32 b),a.neg32.fma32 b c,[{path := [],side := .right,combine := .subtract}],rfl⟩

-- Distinct child plans, unchanged siblings and a nonempty leading retain order.
example (op : Symbol) (leading a b c d : Term Nat) :
    contractAll (childrenEdits 1 [[{path := [],side := .left}],[],
      [{path := [],side := .right,combine := .subtract}]])
      (.app op [leading,(a.mul32 b).add c,d,c.sub32 (a.mul32 b)]) =
      some (.app op [leading,a.fma32 b c,d,a.neg32.fma32 b c]) := by
  exact contractAll_children op [leading] [fused a b c,.keep d,difference a b c]

-- All four operands of a whole-tile sum remain present, including repetition
-- and explicit padding. The plan is lifted beneath the unchanged BF16 cast.
private def fullSum : Symbol := .reduceSum (some .fp32) [2,2] ⟨1,by decide⟩ Bool.false (⟨0,by decide⟩,())

example (a b c padding : Term Nat) :
    let plan := ChildContraction.app (.cast (some .fp32) .real .bf16)
      [ChildContraction.app fullSum [fused a b c,.keep padding,fused a b c,difference a b c]]
    contractAll plan.edits plan.source = some plan.target := by
  exact ChildContraction.accepted _

example (a b c padding : Term Nat) :
    (ChildContraction.app fullSum [fused a b c,.keep padding,fused a b c,difference a b c]).source.inputs.Perm
      (ChildContraction.app fullSum [fused a b c,.keep padding,fused a b c,difference a b c]).target.inputs :=
  ChildContraction.inputs_perm _

-- Lifting does not permit an edit across a cast or outside the argument list.
example (a b c : Term Nat) :
    contractAll (childrenEdits 0 [[{path := [],side := .left}]])
      (.app fullSum [(Term.app (.cast (some .fp32) .real .bf16) [a.mul32 b]).add c]) = none := rfl

example (a b c : Term Nat) :
    contractAll (childrenEdits 1 [[{path := [],side := .left}]])
      (.app fullSum [(a.mul32 b).add c]) = none := rfl

example (a b c : Term Nat) :
    contractAll (childrenEdits 0 [[{path := [],side := .right}]])
      (.app fullSum [c.sub32 (a.mul32 b)]) = none := rfl

example (a : Term Nat) :
    contractAll (childrenEdits 1 []) (.app fullSum [a]) = some (.app fullSum [a]) := rfl

example (a b c : Term Nat) :
    let first := ChildContraction.app (.binary (some .fp32) .real .mul) [.keep a,fused a b c]
    let sum := ChildContraction.app (.binary (some .fp32) .real .add) [first,.keep c]
    let result := sum.andThen [{path := [],side := .left}] (a.fma32 (a.fma32 b c) c) rfl
    contractAll result.edits result.source = some result.target := by
  exact ChildContraction.accepted _
