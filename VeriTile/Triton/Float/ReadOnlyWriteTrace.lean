import VeriTile.Triton.Float.AtomicInterleavingTraceComposition

/-! Source fragments that cannot write any region have an empty primitive
write trace, including nested source loops and branches. Their computations
and register effects still execute through the actual source semantics. -/
namespace VeriTile.Triton.FP.Structural
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Inhabited α]

theorem algReadOnly_writeEvents_empty (M : Algebra α) (statement : Stmt) (state : State α)
    (confined : algReadOnly (fun _ => True) statement) : algWriteEvents M statement state = some [] := by
  cases statement with
  | assign => rfl
  | store dtype shape access value mask | atomicAdd dtype shape access value mask =>
      cases access <;> simp [algReadOnly,accessOutside] at confined
  | atomicRMW operation dtype shape access value extra mask result =>
      cases extra <;> cases result <;> cases access <;> simp [algReadOnly,accessOutside] at confined
  | forLoop | forRange | forRangeDyn | forRangeInt | ifThen | ifThenElse => simp [algReadOnly] at confined

theorem readOnly_leaf_writeEvents_empty (M : Algebra α) (statement : ComputeStmt) (state : State α)
    (confined : readOnly (fun _ => True) statement) (supported : Interleaved.leafSupported statement = true) : leafWriteEvents M statement state = some [] := by
  cases statement with
  | alg statement => exact algReadOnly_writeEvents_empty M statement state (by simpa only [readOnly] using confined)
  | assign => rfl
  | store dtype shape access value mask | atomicAdd dtype shape access value mask =>
      cases access <;> simp [readOnly,accessOutside] at confined
  | atomicRMW operation dtype shape access value extra mask result =>
      cases extra <;> cases result <;> cases access <;> simp [readOnly,accessOutside] at confined
  | forLoop | forRange | forRangeDyn | forRangeInt | ifThen | ifThenElse =>
      simp [Interleaved.leafSupported] at supported
  | effectMarker => simp [readOnly] at confined

namespace Interleaved

theorem Local.readOnly_writeEvents_empty (M : Algebra α) (before : Local α) (memory : Memory α)
    (confined : pendingReadOnly (fun _ => True) before.pending) : before.writeEvents M memory = some [] := by
  obtain ⟨code,state⟩ := before
  cases code with
  | nil => rfl
  | cons command rest =>
    cases command with
    | source statement =>
      by_cases leaf : leafSupported statement = true
      · simp only [writeEvents,leaf,ite_true]
        exact readOnly_leaf_writeEvents_empty M statement _ ((pendingReadOnly_cons _ _ _).mp confined).1 leaf
      · simp [writeEvents,leaf]
    | counted | natural | integer => rfl

theorem Local.Advances.readOnly_writeTrace (M : Algebra α) {before after : Local α}
    (advanced : before.Advances M after) (confined : pendingReadOnly (fun _ => True) before.pending) :
    before.WriteAdvances M [] after ∧ pendingReadOnly (fun _ => True) after.pending := by
  induction advanced with
  | refl => exact ⟨Local.WriteAdvances.refl,confined⟩
  | @tail first last earlier ticked ih =>
      obtain ⟨traced,readOnly⟩ := ih
      refine ⟨?_,(Local.tick_readOnly M (fun _ => True) first last first.state.mem readOnly ticked).1⟩
      simpa only [List.append_nil] using traced.tail ticked (Local.readOnly_writeEvents_empty M first first.state.mem readOnly)

theorem readOnly_body_writeTrace (M : Algebra α) (body : List ComputeStmt) (initial final : State α)
    (supported : ∀ statement ∈ body, Supported statement) (confined : readOnlyBody (fun _ => True) body)
    (executed : Structural.run M body initial = some final) :
    (Local.mk (commands body) initial).WriteAdvances M [] ⟨[],final⟩ := by
  have advanced := supported_body_completes M body supported initial final executed
  exact (advanced.readOnly_writeTrace M ((commands_readOnly (fun _ => True) body).mpr confined)).1

#axiomsClean algReadOnly_writeEvents_empty
#axiomsClean readOnly_leaf_writeEvents_empty
#axiomsClean Local.readOnly_writeEvents_empty
#axiomsClean Local.Advances.readOnly_writeTrace
#axiomsClean readOnly_body_writeTrace
end Interleaved
end
end VeriTile.Triton.FP.Structural
