import VeriTile.Triton.DSL.CallSignature
import VeriTile.Meta.StatementAudit

/-! Signature-driven store conversions must survive bounded loops without
allowing iteration-local pointer evidence to escape its scope. -/
namespace VeriTile.Tests.StaticStoreCasts
open VeriTile.Triton
noncomputable section

def signature : CallSignature where
  floatingPointers := [("X",.fp32),("Y",.bf16)]
  constexpr := ["N"]

def source (X Y : RegionName) (N : Nat) : ComputeKernel :=
  with_triton_signature signature in triton {
    value = tl.load(X)
    for i in tl.static_range(2) {
      p = Y + i
      tl.store(p, value)
    }
    for j in tl.static_range($(N)) {
      if j < N {
        tl.store(Y + j, value, mask=j < N)
      }
    }
  }

def expected (X Y : RegionName) (N : Nat) : ComputeKernel :=
  let dtype : FloatDType := .fp32
  let out_dtype : FloatDType := .bf16
  triton {
  tl.region X = DTYPE, Y = OUT_DTYPE
  value = tl.load(X)
  for i in tl.static_range(2) {
    p = Y + i
    tl.store(p, (value).to(OUT_DTYPE))
  }
  for j in tl.static_range($(N)) {
    if j < $(N) {
      tl.store(Y + j, (value).to(OUT_DTYPE), mask=j < $(N))
    }
  }
}

theorem loop_masks_and_casts (X Y : RegionName) (N : Nat) :
    source X Y N = expected X Y N := rfl

def aliases (X Y : RegionName) (N : Nat) : ComputeKernel :=
  with_triton_signature signature in triton {
    value = tl.load(X)
    tl.static_range i in 2 {
      tl.store(Y + i, value)
    }
    tl.static_range j in $(N) {
      tl.store(Y + j, value)
    }
  }

def aliasesExpected (X Y : RegionName) (N : Nat) : ComputeKernel :=
  let dtype : FloatDType := .fp32
  let out_dtype : FloatDType := .bf16
  triton {
  tl.region X = DTYPE, Y = OUT_DTYPE
  value = tl.load(X)
  tl.static_range i in 2 {
    tl.store(Y + i, (value).to(OUT_DTYPE))
  }
  tl.static_range j in $(N) {
    tl.store(Y + j, (value).to(OUT_DTYPE))
  }
}

theorem surface_aliases_keep_casts (X Y : RegionName) (N : Nat) :
    aliases X Y N = aliasesExpected X Y N := rfl

/-- error: pointer alias is rebound under runtime control flow -/
#guard_msgs in
def rebound (X Y : RegionName) : ComputeKernel :=
  with_triton_signature signature in triton {
    p = Y
    for i in tl.static_range(2) {
      p = X
      tl.store(p, tl.load(X))
    }
  }

/-- error: loop index shadows a pointer alias -/
#guard_msgs in
def shadowIndex (X Y : RegionName) : ComputeKernel :=
  with_triton_signature signature in triton {
    p = Y
    for p in tl.static_range(2) {
      tl.store(p, tl.load(X))
    }
  }

/-- error: pointer parameter p is missing from the call signature -/
#guard_msgs in
def escaped (X Y : RegionName) : ComputeKernel :=
  with_triton_signature signature in triton {
    for i in tl.static_range(0) {
      p = Y
    }
    tl.store(p, tl.load(X))
  }

#axiomsClean loop_masks_and_casts
#axiomsClean surface_aliases_keep_casts
end
end VeriTile.Tests.StaticStoreCasts
