import VeriTile.Triton.DSL
import VeriTile.Triton.Float.RegisterFrame

namespace VeriTile.Tests.RegisterFrame
open VeriTile.Triton FP.Structural
noncomputable section
set_option allowUnsafeReducibility true
attribute [local reducible] ComputeDType.eraseDType

def body (X Y : RegionName) : ComputeKernel := triton {
  tl.region X = tl.float32, Y = tl.bfloat16
  value = tl.load(X)
  if tl.program_id(0) == 0 {
    temporary = value * value
    tl.store(Y, temporary.to(tl.bfloat16))
  } else {
    tl.store(Y, value.to(tl.bfloat16))
  }
}

theorem checked (X Y : RegionName) :
    registersUntouched "saved" (body X Y).surfaceBody = Bool.true := by simp [body,ComputeKernel.surfaceBody,registersUntouched,registerUntouched]

theorem unchanged {α : Type} [Inhabited α] (M : Algebra α) (X Y : RegionName)
    (initial final : State α) (ran : exec M (body X Y) initial = some final)
    (dtype : TileDType) (shape : TileShape) :
    final.regs dtype shape "saved" = initial.regs dtype shape "saved" :=
  run_register_frame M "saved" _ (checked X Y) initial final ran dtype shape

example : registerUntouched "saved" (.assign .nat [] "saved" (.alg (.constNat 0))) = Bool.false := by simp [registerUntouched]
example : registerUntouched "saved" (.ifThen (.constBool Bool.false)
    [.assign .nat [] "saved" (.alg (.constNat 0))]) = Bool.false := by simp [registersUntouched,registerUntouched]
example : registerUntouched "saved" (.forLoop "i" 0 []) = Bool.false := by simp [registerUntouched]
example : registersUntouched "saved"
    [.assign .nat [] "other" (.alg (.constNat 0)),
     .assign .bool [] "saved" (.alg (.constBool Bool.true))] = Bool.false := by simp [registersUntouched,registerUntouched]

#axiomsClean checked
#axiomsClean unchanged
end
end VeriTile.Tests.RegisterFrame
