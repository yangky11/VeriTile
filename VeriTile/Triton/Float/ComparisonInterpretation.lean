import VeriTile.Triton.Float.ValueTransport

/-! Interpret floating comparisons on a different scalar carrier. Symbolic
arithmetic can retain its expression trees while branches use the declared
numerical interpretation of their operands. Precision, dtype and unavailable
callbacks are preserved; no order or NaN law is assumed. -/
namespace VeriTile.Triton.FP.Structural
variable {α β : Type}

/-- Only comparison callbacks change. In particular, this does not assume
that an entire expression or program commutes with the interpretation. -/
def Algebra.withInterpretedComparisons (base : Algebra α) (target : Algebra β)
    (evaluate : α → β) : Algebra α :=
  { base with
    compareLt := fun p d => (target.compareLt p d).map fun cmp a b => cmp (evaluate a) (evaluate b)
    compareLe := fun p d => (target.compareLe p d).map fun cmp a b => cmp (evaluate a) (evaluate b)
    compareEq := fun p d => (target.compareEq p d).map fun cmp a b => cmp (evaluate a) (evaluate b) }

theorem numericLt_interpreted (base : Algebra α) (target : Algebra β) (evaluate : α → β)
    (p : Option ComputeDType) {dtype : TileDType} (kind : ComparableDType dtype) :
    numericLt (base.withInterpretedComparisons target evaluate) p kind =
      (numericLt target p kind).map (fun cmp a b =>
        cmp (mapValue evaluate dtype a) (mapValue evaluate dtype b)) := by
  cases kind <;> rfl

theorem numericLe_interpreted (base : Algebra α) (target : Algebra β) (evaluate : α → β)
    (p : Option ComputeDType) {dtype : TileDType} (kind : ComparableDType dtype) :
    numericLe (base.withInterpretedComparisons target evaluate) p kind =
      (numericLe target p kind).map (fun cmp a b =>
        cmp (mapValue evaluate dtype a) (mapValue evaluate dtype b)) := by
  cases kind <;> rfl

theorem numericEq_interpreted (base : Algebra α) (target : Algebra β) (evaluate : α → β)
    (p : Option ComputeDType) {dtype : TileDType} (kind : ComparableDType dtype) :
    numericEq (base.withInterpretedComparisons target evaluate) p kind =
      (numericEq target p kind).map (fun cmp a b =>
        cmp (mapValue evaluate dtype a) (mapValue evaluate dtype b)) := by
  cases kind <;> rfl

section
variable [Inhabited α]
set_option backward.isDefEq.respectTransparency false

/-- Evaluate the actual operand expressions before comparing their interpreted
values. The broadcast coordinates remain those of the source comparison. -/
theorem gt_interpreted (base : Algebra α) (target : Algebra β) (evaluate : α → β)
    (p : Option ComputeDType) (s : State α) {dtype : TileDType}
    (kind : ComparableDType dtype) {left right shape : TileShape} (bc : Broadcast left right shape)
    (a : Op dtype left) (b : Op dtype right) (av : Values α dtype left) (bv : Values α dtype right)
    (cmp : Value β dtype → Value β dtype → Bool)
    (supported : numericLt target p kind = some cmp)
    (ha : evalOp (base.withInterpretedComparisons target evaluate) p a s = some av)
    (hb : evalOp (base.withInterpretedComparisons target evaluate) p b s = some bv) :
    evalOp (base.withInterpretedComparisons target evaluate) p (.gt kind bc a b) s =
      some (fun i => cmp (mapValue evaluate dtype (bv (bc.rightIndex i)))
        (mapValue evaluate dtype (av (bc.leftIndex i)))) := by
  rw [evalOp_unfold]
  simp only [numericLt_interpreted,supported,Option.map_some,ha,hb]
  rfl

theorem ge_interpreted (base : Algebra α) (target : Algebra β) (evaluate : α → β)
    (p : Option ComputeDType) (s : State α) {dtype : TileDType}
    (kind : ComparableDType dtype) {left right shape : TileShape} (bc : Broadcast left right shape)
    (a : Op dtype left) (b : Op dtype right) (av : Values α dtype left) (bv : Values α dtype right)
    (cmp : Value β dtype → Value β dtype → Bool)
    (supported : numericLe target p kind = some cmp)
    (ha : evalOp (base.withInterpretedComparisons target evaluate) p a s = some av)
    (hb : evalOp (base.withInterpretedComparisons target evaluate) p b s = some bv) :
    evalOp (base.withInterpretedComparisons target evaluate) p (.ge kind bc a b) s =
      some (fun i => cmp (mapValue evaluate dtype (bv (bc.rightIndex i)))
        (mapValue evaluate dtype (av (bc.leftIndex i)))) := by
  rw [evalOp_unfold]
  simp only [numericLe_interpreted,supported,Option.map_some,ha,hb]
  rfl

/-- Self-inequality can classify NaNs even when the symbolic operands are
syntactically identical. Equality is never replaced by structural equality. -/
theorem ne_interpreted (base : Algebra α) (target : Algebra β) (evaluate : α → β)
    (p : Option ComputeDType) (s : State α) {dtype : TileDType}
    (kind : ComparableDType dtype) {left right shape : TileShape} (bc : Broadcast left right shape)
    (a : Op dtype left) (b : Op dtype right) (av : Values α dtype left) (bv : Values α dtype right)
    (cmp : Value β dtype → Value β dtype → Bool)
    (supported : numericEq target p kind = some cmp)
    (ha : evalOp (base.withInterpretedComparisons target evaluate) p a s = some av)
    (hb : evalOp (base.withInterpretedComparisons target evaluate) p b s = some bv) :
    evalOp (base.withInterpretedComparisons target evaluate) p (.ne kind bc a b) s =
      some (fun i => !(cmp (mapValue evaluate dtype (av (bc.leftIndex i)))
        (mapValue evaluate dtype (bv (bc.rightIndex i))))) := by
  rw [evalOp_unfold]
  simp only [numericEq_interpreted,supported,Option.map_some,ha,hb]
  rfl
end

#axiomsClean numericLt_interpreted
#axiomsClean numericLe_interpreted
#axiomsClean numericEq_interpreted
#axiomsClean gt_interpreted
#axiomsClean ge_interpreted
#axiomsClean ne_interpreted
end VeriTile.Triton.FP.Structural
