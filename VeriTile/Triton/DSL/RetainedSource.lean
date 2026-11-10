import VeriTile.Triton.DSL.CallSignature

/-! Retain one raw source quotation alongside its ordinary call-signature
elaboration. This is source provenance tooling, not a correctness theorem or a
compiler certificate. The kernel is still elaborated by `with_triton_signature`;
no source statement, conversion, mask or control-flow node is rewritten here. -/
namespace VeriTile.Triton

structure RetainedSource where
  /-- Original raw quotation, including its outer braces and whitespace. -/
  text : String
  kernel : ComputeKernel

namespace DSL.RetainedSource
open Lean Elab Term Meta

syntax (name := retainedSource) "retain_triton_signature " term " in " "triton " RawSourceText.body : term

@[term_elab retainedSource] def elaborateRetainedSource : TermElab := fun stx expected => do
  let profile : TSyntax `term := ⟨stx[1]⟩
  let raw := stx.getArgs.back!
  let quoted : TSyntax `term := ⟨Syntax.mkStrLit raw.getAtomVal⟩
  let kernel : TSyntax `term := ⟨mkNode ``CallSignature.withSignature #[
    mkAtom "with_triton_signature", profile.raw, mkAtom "in", mkAtom "triton", raw]⟩
  let result ← `(VeriTile.Triton.RetainedSource.mk $quoted $kernel)
  elabTerm result expected

/-- Extract the literal retained text during elaboration. The resulting String
is executable even when the accompanying semantic kernel is noncomputable.
Reject a value whose text cannot be reduced to a literal; do not evaluate IO or
an external file while constructing the source identity. -/
syntax (name := sourceText) "triton_source_text " term : term

@[term_elab sourceText] def elaborateSourceText : TermElab := fun stx expected => do
  let source ← elabTermEnsuringType stx[1] (mkConst ``Triton.RetainedSource)
  let value ← withTransparency .all <| reduce (← mkAppM ``Triton.RetainedSource.text #[source])
  let .lit (.strVal text) := value
    | throwErrorAt stx "retained Triton text must reduce to a string literal"
  elabTerm (Syntax.mkStrLit text) expected

end DSL.RetainedSource
end VeriTile.Triton
