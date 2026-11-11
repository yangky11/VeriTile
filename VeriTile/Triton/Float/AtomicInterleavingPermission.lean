import VeriTile.Triton.Float.AtomicInterleavingControlMemory
import VeriTile.Triton.Float.AtomicInterleavingDependencies
import VeriTile.Triton.Float.SourceWritePermission

/-! Checked footprints for one actual scheduled source instruction. Ordinary
and atomic writes remain distinct, including under input-preserving interference. -/
namespace VeriTile.Triton.FP.Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

theorem algWritePermitted_iff (M : Algebra α) (regions : RegionName → Prop)
    (ordinary atomic : RegionName → Nat → Prop) (statement : Stmt)
    (dependency : algDependencies regions statement) (first second : State α)
    (same : first.AgreesOn regions second) :
    algWritePermitted M ordinary atomic statement first ↔ algWritePermitted M ordinary atomic statement second := by
  unfold algWritePermitted
  split
  · rfl
  · exact writePermitted_iff M regions ordinary _ _ dependency.1 dependency.2.1 first second same
  · exact writePermitted_iff M regions atomic _ _ dependency.1 dependency.2.1 first second same
  · exact writePermitted_iff _ regions atomic _ _ dependency.1 dependency.2.1 first second same
  · rfl

theorem leafWritePermitted_iff (M : Algebra α) (regions : RegionName → Prop)
    (ordinary atomic : RegionName → Nat → Prop) (statement : ComputeStmt)
    (dependency : readDependencies regions statement) (supported : Interleaved.leafSupported statement = true)
    (first second : State α) (same : first.AgreesOn regions second) :
    leafWritePermitted M ordinary atomic statement first ↔ leafWritePermitted M ordinary atomic statement second := by
  cases statement with
  | alg statement =>
      simp only [readDependencies] at dependency
      exact algWritePermitted_iff M regions ordinary atomic statement dependency first second same
  | assign => rfl
  | store dtype shape access expression mask =>
      simp only [readDependencies] at dependency
      exact writePermitted_iff M regions ordinary access mask dependency.1 dependency.2.1 first second same
  | atomicAdd numeric shape access expression mask =>
      simp only [readDependencies] at dependency
      exact writePermitted_iff M regions atomic access mask dependency.1 dependency.2.1 first second same
  | atomicRMW operation dtype shape access expression result mask order =>
      cases result <;> cases order <;> try { simp [Interleaved.leafSupported] at supported }
      simp only [readDependencies] at dependency
      exact writePermitted_iff _ regions atomic access mask dependency.1 dependency.2.1 first second same
  | forLoop | forRange | forRangeDyn | forRangeInt | ifThen | ifThenElse | effectMarker =>
      simp [Interleaved.leafSupported] at supported

namespace Interleaved

def Local.Permitted (M : Algebra α) (ordinary atomic : RegionName → Nat → Prop)
    (thread : Local α) (memory : Memory α) : Prop :=
  match thread.pending with
  | .source statement :: _ => if leafSupported statement then
      leafWritePermitted M ordinary atomic statement { thread.state with mem := memory } else True
  | _ => True

theorem Local.permitted_agrees (M : Algebra α) (regions : RegionName → Prop)
    (ordinary atomic : RegionName → Nat → Prop) (code : List Command)
    (dependent : pendingDependencies regions code) (first second : State α)
    (same : first.AgreesOn regions second) :
    (Local.mk code first).Permitted M ordinary atomic first.mem ↔
      (Local.mk code second).Permitted M ordinary atomic second.mem := by
  cases code with
  | nil => rfl
  | cons command rest =>
    cases command with
    | counted | natural | integer => rfl
    | source statement =>
      by_cases supported : leafSupported statement = true
      · simp only [Permitted,supported,ite_true]
        exact leafWritePermitted_iff M regions ordinary atomic statement
          ((pendingDependencies_cons regions (.source statement) rest).mp dependent).1 supported first second same
      · simp [Permitted,supported]

theorem Local.tick_permission_frame (M : Algebra α) (ordinary atomic : RegionName → Nat → Prop)
    (before after : Local α) (memory : Memory α) (permitted : before.Permitted M ordinary atomic memory)
    (ran : before.tick M memory = some after) :
    ∀ region offset, ¬ ordinary region offset → ¬ atomic region offset → after.state.mem region offset = memory region offset := by
  by_cases control : leafHead before.pending = false
  · intro region offset _ _
    rw [before.tick_control_memory M after memory control ran]
  · obtain ⟨code,state⟩ := before
    cases code with
    | nil => simp [leafHead] at control
    | cons command rest =>
      cases command with
      | counted | natural | integer => simp [leafHead] at control
      | source statement =>
        have supported : leafSupported statement = true := Bool.eq_true_of_not_eq_false control
        simp only [Permitted,supported,ite_true] at permitted
        cases advanced : step M statement { state with mem := memory } with
        | none => simp [tick,supported,advanced] at ran
        | some next =>
          simp [tick,supported,advanced] at ran
          subst after
          intro region offset ordinaryOutside atomicOutside
          exact leafWritePermitted_frame M ordinary atomic statement _ next permitted supported advanced
            region offset ⟨ordinaryOutside,atomicOutside⟩

#axiomsClean Local.permitted_agrees
#axiomsClean Local.tick_permission_frame
end Interleaved
#axiomsClean algWritePermitted_iff
#axiomsClean leafWritePermitted_iff
end
end VeriTile.Triton.FP.Structural
