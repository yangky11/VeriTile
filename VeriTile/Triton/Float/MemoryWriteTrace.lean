import VeriTile.Triton.Float.CellWriteSemantics

/-! Primitive memory-write traces retain lane order and distinguish stores
from atomic updates. Atomic operands are evaluated before the write; the old
word is read when the event is applied. No commutation law is assumed. -/
namespace VeriTile.Triton.FP.Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false

inductive AtomicKind where
  | add
  | reduce (operation : RMWOp)

inductive MemoryWrite (α : Type) where
  | store (region : RegionName) (offset : Nat) (value : Cell α)
  | atomic (kind : AtomicKind) (region : RegionName) (offset : Nat) (dtype : TileDType)
      (combine : Value α dtype → Value α dtype → Value α dtype) (value : Value α dtype)

namespace MemoryWrite
variable {α : Type} [Inhabited α]

def apply (event : MemoryWrite α) (state : State α) : State α :=
  match event with
  | .store region offset value => state.write region offset value
  | .atomic _ region offset dtype combine value =>
      state.write region offset (.mk dtype (combine ((state.mem region offset).read dtype) value))

def applyAll (events : List (MemoryWrite α)) (state : State α) : State α :=
  events.foldl (fun current event => event.apply current) state

def lanes {ι : Type} (indices : List ι) (active : ι → Bool) (event : ι → MemoryWrite α) : List (MemoryWrite α) :=
  indices.filterMap (fun i => if active i then some (event i) else none)

theorem lanes_apply {ι : Type} (indices : List ι) (active : ι → Bool) (event : ι → MemoryWrite α) (state : State α) :
    applyAll (lanes indices active event) state =
      indices.foldl (fun current i => if active i then (event i).apply current else current) state := by
  induction indices generalizing state with
  | nil => rfl
  | cons i rest ih =>
      cases selected : active i
      · simpa [lanes,applyAll,selected] using ih state
      · simpa [lanes,applyAll,selected] using ih ((event i).apply state)

theorem applyAll_append (first second : List (MemoryWrite α)) (state : State α) :
    applyAll (first ++ second) state = applyAll second (applyAll first state) := by
  simp only [applyAll,List.foldl_append]

theorem apply_memory (event : MemoryWrite α) (first second : State α) (memory : first.mem = second.mem) :
    (event.apply first).mem = (event.apply second).mem := by
  cases event <;> simp only [apply,State.write,memory]

theorem applyAll_memory (events : List (MemoryWrite α)) (first second : State α) (memory : first.mem = second.mem) :
    (applyAll events first).mem = (applyAll events second).mem := by
  induction events generalizing first second with
  | nil => exact memory
  | cons event rest ih => exact ih _ _ (apply_memory event first second memory)

/-- Project the ordered write trace onto one cell, retaining the actual seed. -/
def atCell (event : MemoryWrite α) (region : RegionName) (offset : Nat) (old : Cell α) : Cell α :=
  match event with
  | .store target address value => if region = target ∧ offset = address then value else old
  | .atomic _ target address dtype combine value =>
      if region = target ∧ offset = address then .mk dtype (combine (old.read dtype) value) else old

theorem apply_read (event : MemoryWrite α) (region : RegionName) (offset : Nat) (state : State α) :
    (event.apply state).mem region offset = event.atCell region offset (state.mem region offset) := by
  cases event with
  | store target address value =>
      by_cases selected : region = target ∧ offset = address
      · rcases selected with ⟨rfl,rfl⟩; simp [apply,atCell]
      · simp only [apply,atCell,selected,ite_false]
        exact State.write_other _ _ _ _ _ _ (not_and_or.mp selected)
  | atomic kind target address dtype combine value =>
      by_cases selected : region = target ∧ offset = address
      · rcases selected with ⟨rfl,rfl⟩; simp [apply,atCell]
      · simp only [apply,atCell,selected,ite_false]
        exact State.write_other _ _ _ _ _ _ (not_and_or.mp selected)

theorem applyAll_read (events : List (MemoryWrite α)) (region : RegionName) (offset : Nat) (state : State α) :
    (applyAll events state).mem region offset =
      events.foldl (fun old event => event.atCell region offset old) (state.mem region offset) := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      change (applyAll rest (event.apply state)).mem region offset = _
      rw [ih,apply_read]
      rfl

end MemoryWrite

variable {α : Type} [Inhabited α]

def storeEvents (M : Algebra α) (region : Region dtype) (offset : Op .nat shape)
    (mask : MaskOpt dtype shape) (values : Values α dtype shape) (state : State α) : Option (List (MemoryWrite α)) := do
  let offsets ← evalOp M none offset state
  let active ← writeMask M mask state
  return MemoryWrite.lanes (TileShape.allIndices shape) active
    (fun lane => .store (Region.cast region) (offsets lane) (.mk dtype (values lane)))

def atomicEvents (M : Algebra α) (kind : AtomicKind) (numeric : NumericDType dtype)
    (region : Region dtype) (offset : Op .nat shape) (mask : MaskOpt dtype shape)
    (values : Values α dtype shape) (state : State α) : Option (List (MemoryWrite α)) := do
  let combine ← atomicAddition M numeric
  let offsets ← evalOp M none offset state
  let active ← writeMask M mask state
  return MemoryWrite.lanes (TileShape.allIndices shape) active
    (fun lane => .atomic kind (Region.cast region) (offsets lane) dtype combine (values lane))

theorem store_region_events (M : Algebra α) (region : Region dtype) (offset : Op .nat shape)
    (mask : MaskOpt dtype shape) (values : Values α dtype shape) (state : State α) :
    store M (.region region offset) mask values state =
      (storeEvents M region offset mask values state).map (fun events => MemoryWrite.applyAll events state) := by
  rw [store_region_eq]
  cases addresses : evalOp M none offset state <;> cases active : writeMask M mask state <;>
    simp [storeEvents,addresses,active,MemoryWrite.lanes_apply,MemoryWrite.apply]

theorem atomicAdd_region_events (M : Algebra α) (numeric : NumericDType dtype) (kind : AtomicKind)
    (region : Region dtype) (offset : Op .nat shape) (mask : MaskOpt dtype shape)
    (values : Values α dtype shape) (state : State α) :
    atomicAdd M numeric (.region region offset) mask values state =
      (atomicEvents M kind numeric region offset mask values state).map (fun events => MemoryWrite.applyAll events state) := by
  rw [atomicAdd_region_eq]
  cases available : atomicAddition M numeric <;> cases addresses : evalOp M none offset state <;>
    cases active : writeMask M mask state <;>
    simp [atomicEvents,available,addresses,active,MemoryWrite.lanes_apply,MemoryWrite.apply]

def atomicReductionEvents (M : Algebra α) (operation : RMWOp) :
    {dtype : TileDType} → {shape : TileShape} → Region dtype → Op .nat shape → MaskOpt dtype shape →
    Values α dtype shape → State α → Option (List (MemoryWrite α)) :=
  fun {dtype} {_} region offset mask values state =>
    if operation = .max ∨ operation = .min then
      let backend := { M with atomicAdd := M.atomicReduce operation }
      match dtype,region,mask,values with
      | .real,region,mask,values => atomicEvents backend (.reduce operation) .real region offset mask values state
      | .fp32,region,mask,values => atomicEvents backend (.reduce operation) .fp32 region offset mask values state
      | .fp16,region,mask,values => atomicEvents backend (.reduce operation) .fp16 region offset mask values state
      | .bf16,region,mask,values => atomicEvents backend (.reduce operation) .bf16 region offset mask values state
      | .f8e4,region,mask,values => atomicEvents backend (.reduce operation) .f8e4 region offset mask values state
      | .f8e5,region,mask,values => atomicEvents backend (.reduce operation) .f8e5 region offset mask values state
      | _,_,_,_ => none
    else none

theorem atomicReduction_region_events (M : Algebra α) (operation : RMWOp)
    (region : Region dtype) (offset : Op .nat shape) (mask : MaskOpt dtype shape)
    (values : Values α dtype shape) (state : State α) :
    atomicReduction M operation (.region region offset) mask values state =
      (atomicReductionEvents M operation region offset mask values state).map (fun events => MemoryWrite.applyAll events state) := by
  cases dtype <;> cases operation <;>
    simp [atomicReduction,atomicReductionEvents]
  all_goals exact atomicAdd_region_events _ _ _ _ _ _ _ _

#axiomsClean MemoryWrite.apply_read
#axiomsClean MemoryWrite.applyAll_read
#axiomsClean atomicReduction_region_events
#axiomsClean MemoryWrite.lanes_apply
#axiomsClean MemoryWrite.applyAll_append
#axiomsClean MemoryWrite.apply_memory
#axiomsClean MemoryWrite.applyAll_memory
#axiomsClean store_region_events
#axiomsClean atomicAdd_region_events
end
end VeriTile.Triton.FP.Structural
