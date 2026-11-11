import VeriTile.Triton.Float.Equational
import VeriTile.Triton.Float.ValueTransport

/-! Interpretation of typed memory inputs. Every floating storage format is
covered, while launch coordinates remain discrete. This is an input relation,
not an assumed correspondence between complete program executions. -/
namespace VeriTile.Triton.FP.Equational
open Structural
variable {Atom Scalar : Type} [Inhabited Atom] [Inhabited Scalar]

structure MemoryEvaluation (evaluate : Term Atom → Scalar)
    (source : State (Term Atom)) (target : State Scalar) : Prop where
  ids : source.pids = target.pids
  words : ∀ (dtype : FloatDType) (region : RegionName) (offset : Nat),
    evaluate (toFloat dtype ((source.mem region offset).read dtype.toTileDType)) =
      toFloat dtype ((target.mem region offset).read dtype.toTileDType)

omit [Inhabited Atom] in
theorem reify_memory (calls : Symbol → List Scalar → Scalar) (state : State Scalar) :
    MemoryEvaluation (Term.evaluate id calls) (state.map Term.leaf) state := by
  refine ⟨rfl,?_⟩
  intro dtype region offset
  rw [State.map_read Term.leaf (by rfl)]
  simp only [Term.evaluate,id_eq]

theorem MemoryEvaluation.transport {evaluate : Term Atom → Scalar}
    {source source' : State (Term Atom)} {target target' : State Scalar}
    (inputs : MemoryEvaluation evaluate source target)
    (sourceWords : source'.mem = source.mem) (targetWords : target'.mem = target.mem)
    (ids : source'.pids = target'.pids) : MemoryEvaluation evaluate source' target' := by
  refine ⟨ids,?_⟩
  intro dtype region offset
  rw [sourceWords,targetWords]
  exact inputs.words dtype region offset

#axiomsClean reify_memory
#axiomsClean MemoryEvaluation.transport
end VeriTile.Triton.FP.Equational
