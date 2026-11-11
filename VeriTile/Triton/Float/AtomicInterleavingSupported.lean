import VeriTile.Triton.Float.AtomicInterleavingLoops

/-! A compositional admitted source subset for statement scheduling. Support
requires actual scalar-atomic leaves and recursively supported control bodies;
it does not admit barriers, asynchronous effects or vector atomics. -/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

inductive Supported : ComputeStmt → Prop where
  | leaf {statement} : leafSupported statement = true → Supported statement
  | counted {index stop body} : (∀ statement ∈ body, Supported statement) → Supported (.forLoop index stop body)
  | natural {index first last stride body} : (∀ statement ∈ body, Supported statement) →
      Supported (.forRange index first last stride body)
  | dynamic {index first last stride body} : (∀ statement ∈ body, Supported statement) →
      Supported (.forRangeDyn index first last stride body)
  | integer {index first last stride body} : (∀ statement ∈ body, Supported statement) →
      Supported (.forRangeInt index first last stride body)
  | branch {condition body} : (∀ statement ∈ body, Supported statement) → Supported (.ifThen condition body)
  | branches {condition yes no} : (∀ statement ∈ yes, Supported statement) →
      (∀ statement ∈ no, Supported statement) → Supported (.ifThenElse condition yes no)

variable {α : Type} [Inhabited α]

theorem supported_completes (M : Algebra α) (statement : ComputeStmt) (supported : Supported statement) :
    ∀ initial final, step M statement initial = some final →
      (Local.mk [.source statement] initial).Advances M ⟨[],final⟩ := by
  induction supported with
  | leaf allowed =>
      intro initial final ran
      exact Local.Advances.single M (by simp [Local.tick,allowed,ran])
  | @counted index stop body bodySupported ih =>
      intro initial final ran
      exact (Local.Advances.single M (by simp [Local.tick,leafSupported])).trans
        (counted_completes M index 0 stop body (body_completes M _ ih) initial final (by simpa only [step] using ran))
  | @natural index first last stride body bodySupported ih =>
      intro initial final ran
      exact (Local.Advances.single M (by simp [Local.tick,leafSupported])).trans
        (natural_completes M index first last stride body (body_completes M _ ih) initial final (by simpa only [step] using ran))
  | @dynamic index first last stride body bodySupported ih =>
      intro initial final ran
      cases firstRead : evalOp M none first initial with
      | none => simp [step,firstRead] at ran
      | some a =>
          cases lastRead : evalOp M none last initial with
          | none => simp [step,firstRead,lastRead] at ran
          | some b =>
              cases strideRead : evalOp M none stride initial with
              | none => simp [step,firstRead,lastRead,strideRead] at ran
              | some delta =>
                  have remaining : range M index (a ()) (b ()) (delta ()) body initial = some final := by
                    simpa [step,firstRead,lastRead,strideRead] using ran
                  exact (Local.Advances.single M (by simp [Local.tick,leafSupported,firstRead,lastRead,strideRead])).trans
                    (natural_completes M _ _ _ _ _ (body_completes M _ ih) initial final remaining)
  | @integer index first last stride body bodySupported ih =>
      intro initial final ran
      cases firstRead : evalOp M none first initial with
      | none => simp [step,firstRead] at ran
      | some a =>
          cases lastRead : evalOp M none last initial with
          | none => simp [step,firstRead,lastRead] at ran
          | some b =>
              cases strideRead : evalOp M none stride initial with
              | none => simp [step,firstRead,lastRead,strideRead] at ran
              | some delta =>
                  have remaining : rangeInt M index (a ()) (b ()) (delta ()) body initial = some final := by
                    simpa [step,firstRead,lastRead,strideRead] using ran
                  exact (Local.Advances.single M (by simp [Local.tick,leafSupported,firstRead,lastRead,strideRead])).trans
                    (integer_completes M _ _ _ _ _ (body_completes M _ ih) initial final remaining)
  | @branch condition body bodySupported ih =>
      intro initial final ran
      cases selected : evalOp M none condition initial with
      | none => simp [step,selected] at ran
      | some flag =>
          cases choice : flag () with
          | false =>
              have same : initial = final := by simpa [step,selected,choice] using ran
              subst final
              exact Local.Advances.single M (by simp [Local.tick,leafSupported,selected,choice])
          | true =>
              have remaining : Structural.run M body initial = some final := by simpa [step,selected,choice] using ran
              exact (Local.Advances.single M (by simp [Local.tick,leafSupported,selected,choice])).trans
                (body_completes M _ ih initial final remaining)
  | @branches condition yes no yesSupported noSupported yesIH noIH =>
      intro initial final ran
      cases selected : evalOp M none condition initial with
      | none => simp [step,selected] at ran
      | some flag =>
          cases choice : flag () with
          | false =>
              have remaining : Structural.run M no initial = some final := by simpa [step,selected,choice] using ran
              exact (Local.Advances.single M (by simp [Local.tick,leafSupported,selected,choice])).trans
                (body_completes M _ noIH initial final remaining)
          | true =>
              have remaining : Structural.run M yes initial = some final := by simpa [step,selected,choice] using ran
              exact (Local.Advances.single M (by simp [Local.tick,leafSupported,selected,choice])).trans
                (body_completes M _ yesIH initial final remaining)

theorem supported_body_completes (M : Algebra α) (body : List ComputeStmt)
    (supported : ∀ statement ∈ body, Supported statement) : BodyCompletes M body :=
  body_completes M body (fun statement inside => supported_completes M statement (supported statement inside))

#axiomsClean supported_completes
#axiomsClean supported_body_completes
end
end VeriTile.Triton.FP.Structural.Interleaved
