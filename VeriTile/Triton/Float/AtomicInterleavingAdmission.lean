import VeriTile.Triton.Float.AtomicInterleavingTotal

/-! A decidable, fail-closed check for the scheduler's compositional source
subset. This check admits control structure only; execution, memory safety and
native ordinary-access independence require their separate proofs. -/
namespace VeriTile.Triton.FP.Structural.Interleaved

mutual
  def checkSupported : ComputeStmt → Bool
    | .forLoop _ _ body | .forRange _ _ _ _ body | .forRangeDyn _ _ _ _ body | .forRangeInt _ _ _ _ body =>
        checkSupportedBody body
    | .ifThen _ body => checkSupportedBody body
    | .ifThenElse _ yes no => checkSupportedBody yes && checkSupportedBody no
    | statement => leafSupported statement
  termination_by statement => sizeOf statement
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def checkSupportedBody : List ComputeStmt → Bool
    | [] => true
    | statement :: rest => checkSupported statement && checkSupportedBody rest
  termination_by body => sizeOf body
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

mutual
  theorem checkSupported_sound (statement : ComputeStmt) (checked : checkSupported statement = true) :
      Supported statement := by
    cases shape : statement with
    | forLoop index stop body => exact .counted (checkSupportedBody_sound body (by simpa only [shape,checkSupported] using checked))
    | forRange index first last stride body => exact .natural (checkSupportedBody_sound body (by simpa only [shape,checkSupported] using checked))
    | forRangeDyn index first last stride body => exact .dynamic (checkSupportedBody_sound body (by simpa only [shape,checkSupported] using checked))
    | forRangeInt index first last stride body => exact .integer (checkSupportedBody_sound body (by simpa only [shape,checkSupported] using checked))
    | ifThen condition body => exact .branch (checkSupportedBody_sound body (by simpa only [shape,checkSupported] using checked))
    | ifThenElse condition yes no =>
        have parts := Bool.and_eq_true_iff.mp (show (_ && _) = true from by simpa only [shape,checkSupported,checkSupportedBody] using checked)
        exact .branches (checkSupportedBody_sound yes parts.1) (checkSupportedBody_sound no parts.2)
    | _ => exact .leaf (by simpa only [shape,checkSupported] using checked)
  termination_by sizeOf statement
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

  theorem checkSupportedBody_sound (body : List ComputeStmt) (checked : checkSupportedBody body = true) :
      ∀ statement ∈ body, Supported statement := by
    cases shape : body with
    | nil => simp
    | cons first rest =>
        have parts := Bool.and_eq_true_iff.mp (show (_ && _) = true from by simpa only [shape,checkSupported,checkSupportedBody] using checked)
        intro statement inside
        rcases List.mem_cons.mp inside with same | inside
        · subst statement
          exact checkSupported_sound first parts.1
        · exact checkSupportedBody_sound rest parts.2 statement inside
  termination_by sizeOf body
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega
end

#axiomsClean checkSupported_sound
#axiomsClean checkSupportedBody_sound
end VeriTile.Triton.FP.Structural.Interleaved
