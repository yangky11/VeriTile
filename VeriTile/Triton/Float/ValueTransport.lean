import VeriTile.Triton.Float.Structural
import VeriTile.Meta.StatementAudit

/-! Transport the floating carrier while preserving discrete values, memory
tags, register shapes and launch coordinates. This supports symbolic input
construction without replacing a program's memory or control semantics. -/
namespace VeriTile.Triton.FP.Structural
variable {α β : Type}

def mapValue (f : α → β) : (dtype : TileDType) → Value α dtype → Value β dtype
  | .real | .fp32 | .fp16 | .bf16 | .f8e4 | .f8e5 => f
  | .nat | .int | .bool | .ptr | .blockPtr => id

theorem mapValue_default [Inhabited α] [Inhabited β] (f : α → β)
    (preserves : f default = default) (dtype : TileDType) :
    mapValue f dtype (defaultValue dtype) = defaultValue dtype := by
  cases dtype <;> first | exact preserves | rfl

theorem toFloat_mapValue (f : α → β) (dtype : FloatDType) (value : Value α dtype.toTileDType) :
    toFloat dtype (mapValue f dtype.toTileDType value) = f (toFloat dtype value) := by
  cases dtype <;> rfl

def Cell.map (f : α → β) : Cell α → Cell β
  | .mk dtype value => .mk dtype (mapValue f dtype value)

theorem Cell.map_read [Inhabited α] [Inhabited β] (f : α → β) (preserves : f default = default)
    (cell : Cell α) (dtype : TileDType) :
    (cell.map f).read dtype = mapValue f dtype (cell.read dtype) := by
  cases cell with | mk stored value =>
    by_cases same : stored = dtype
    · subst stored
      simp only [Cell.map,Cell.read_same]
    · simp [Cell.map,Cell.read,same,mapValue_default f preserves]

def State.map (f : α → β) (state : State α) : State β where
  mem := fun region offset => (state.mem region offset).map f
  regs := fun dtype shape name => (state.regs dtype shape name).map fun values i => mapValue f dtype (values i)
  pids := state.pids
  numPids := state.numPids
  undef := fun dtype region offset => mapValue f dtype (state.undef dtype region offset)

theorem State.map_read [Inhabited α] [Inhabited β] (f : α → β) (preserves : f default = default)
    (state : State α) (dtype : FloatDType) (region : RegionName) (offset : Nat) :
    toFloat dtype (((state.map f).mem region offset).read dtype.toTileDType) =
      f (toFloat dtype ((state.mem region offset).read dtype.toTileDType)) := by
  change toFloat dtype (((state.mem region offset).map f).read dtype.toTileDType) = _
  rw [Cell.map_read f preserves,toFloat_mapValue]

#axiomsClean mapValue_default
#axiomsClean toFloat_mapValue
#axiomsClean Cell.map_read
#axiomsClean State.map_read
end VeriTile.Triton.FP.Structural
