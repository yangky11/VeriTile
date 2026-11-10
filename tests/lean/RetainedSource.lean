import VeriTile.Triton.DSL.RetainedSource
import tests.lean.CallSignature

namespace VeriTile.Tests.RetainedSource
open VeriTile.Triton

noncomputable def retained (X Y : RegionName) (B : Nat) : Triton.RetainedSource :=
  retain_triton_signature CallSignature.signature in triton {
    offsets = tl.arange(0, B).to(tl.int64)
    x = tl.load(X + offsets)
    y = x * gain
    tl.store(Y + offsets, y, mask=offsets < B)
  }

/-- Retention changes neither the full kernel nor implicit storage conversions. -/
theorem kernel_unchanged (X Y : RegionName) (B : Nat) :
    (retained X Y B).kernel = CallSignature.pasted X Y B := rfl

/-- The text is extracted at elaboration, so this declaration is computable. -/
def text : String := triton_source_text (retained "input" "output" 32)

/-- info: «true» -/
#guard_msgs in
#eval text == "{\n    offsets = tl.arange(0, B).to(tl.int64)\n    x = tl.load(X + offsets)\n    y = x * gain\n    tl.store(Y + offsets, y, mask=offsets < B)\n  }"

/-- Names and tile sizes remain call bindings, not substitutions in the source. -/
example (X Y : RegionName) (B : Nat) :
    (retained X Y B).text = text := rfl

/-- error: pointer parameter X is missing from the call signature -/
#guard_msgs in
noncomputable def missingPointer (X : RegionName) : Triton.RetainedSource :=
  retain_triton_signature ({} : Triton.CallSignature) in triton { x = tl.load(X) }

/-- error: retained Triton text must reduce to a string literal -/
#guard_msgs in
def dynamicText (source : Triton.RetainedSource) : String := triton_source_text source

#axiomsClean kernel_unchanged
end VeriTile.Tests.RetainedSource
