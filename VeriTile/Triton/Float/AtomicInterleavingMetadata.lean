import VeriTile.Triton.Float.AtomicInterleavingAdmission

/-! Local source instructions preserve physical program IDs. In particular,
logical tile coordinates in registers do not alter the scheduling identity. -/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {α : Type} [Inhabited α]

omit [Inhabited α] in
private theorem fold_pids {ι : Type} (items : List ι) (update : State α → ι → State α)
    (preserved : ∀ state item, (update state item).pids = state.pids) (initial : State α) :
    (items.foldl update initial).pids = initial.pids := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih => exact (ih _).trans (preserved _ _)

theorem store_pids (M : Algebra α) {dtype : TileDType} {shape : TileShape}
    (memory : MemAccess dtype shape) (mask : MaskOpt dtype shape) (values : Values α dtype shape)
    (initial final : State α) (ran : store M memory mask values initial = some final) : final.pids = initial.pids := by
  cases memory with
  | region region offsets =>
      simp only [store,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at ran
      obtain ⟨addresses,_,active,_,same⟩ := ran
      subst final
      apply fold_pids
      intro state item
      split <;> simp
  | ptr pointer =>
      simp only [store,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at ran
      obtain ⟨addresses,_,active,_,same⟩ := ran
      subst final
      apply fold_pids
      intro state item
      split <;> simp
  | blockPtr pointer checked =>
      simp only [store,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at ran
      obtain ⟨addresses,_,active,_,same⟩ := ran
      subst final
      apply fold_pids
      intro state item
      split <;> simp

theorem atomicAdd_pids (M : Algebra α) {dtype : TileDType} {shape : TileShape}
    (numeric : NumericDType dtype) (memory : MemAccess dtype shape) (mask : MaskOpt dtype shape)
    (values : Values α dtype shape) (initial final : State α)
    (ran : atomicAdd M numeric memory mask values initial = some final) : final.pids = initial.pids := by
  cases memory with
  | region region offsets =>
      simp only [atomicAdd,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at ran
      obtain ⟨combine,_,addresses,_,active,_,same⟩ := ran
      subst final
      apply fold_pids
      intro state item
      split <;> simp
  | ptr pointer =>
      simp only [atomicAdd,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at ran
      obtain ⟨combine,_,addresses,_,active,_,same⟩ := ran
      subst final
      apply fold_pids
      intro state item
      split <;> simp
  | blockPtr pointer checked =>
      simp only [atomicAdd,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at ran
      obtain ⟨combine,_,addresses,_,active,_,same⟩ := ran
      subst final
      apply fold_pids
      intro state item
      split <;> simp

theorem atomicReduction_pids (M : Algebra α) (operation : RMWOp) {dtype : TileDType} {shape : TileShape}
    (memory : MemAccess dtype shape) (mask : MaskOpt dtype shape) (values : Values α dtype shape)
    (initial final : State α) (ran : atomicReduction M operation memory mask values initial = some final) :
    final.pids = initial.pids := by
  unfold atomicReduction at ran
  split at ran
  · cases dtype <;> try { contradiction }
    all_goals exact atomicAdd_pids _ _ _ _ _ _ _ ran
  · simp at ran

theorem stepAlg_pids (M : Algebra α) (statement : Stmt) (initial final : State α)
    (ran : stepAlg M statement initial = some final) : final.pids = initial.pids := by
  unfold stepAlg at ran
  split at ran
  · simp only [bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at ran
    obtain ⟨value,_,same⟩ := ran
    subst final
    rfl
  · obtain ⟨value,_,executed⟩ := Option.bind_eq_some_iff.mp ran
    exact store_pids _ _ _ _ _ _ executed
  · obtain ⟨value,_,executed⟩ := Option.bind_eq_some_iff.mp ran
    exact atomicAdd_pids _ _ _ _ _ _ _ executed
  · obtain ⟨value,_,executed⟩ := Option.bind_eq_some_iff.mp ran
    exact atomicReduction_pids _ _ _ _ _ _ _ executed
  · contradiction

theorem leaf_step_pids (M : Algebra α) (statement : ComputeStmt) (initial final : State α)
    (supported : leafSupported statement = true) (ran : step M statement initial = some final) :
    final.pids = initial.pids := by
  cases statement with
  | alg statement =>
      simp only [step] at ran
      exact stepAlg_pids M statement initial final ran
  | assign dtype shape name expression =>
      simp only [step,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at ran
      obtain ⟨value,_,same⟩ := ran
      subst final
      rfl
  | store dtype shape memory expression mask =>
      simp only [step] at ran
      obtain ⟨value,_,executed⟩ := Option.bind_eq_some_iff.mp ran
      exact store_pids _ _ _ _ _ _ executed
  | atomicAdd numeric shape memory expression mask =>
      simp only [step] at ran
      obtain ⟨value,_,executed⟩ := Option.bind_eq_some_iff.mp ran
      exact atomicAdd_pids _ _ _ _ _ _ _ executed
  | atomicRMW operation dtype shape memory expression result mask order =>
      cases result <;> cases order <;> try { simp [leafSupported] at supported }
      simp only [step] at ran
      obtain ⟨value,_,executed⟩ := Option.bind_eq_some_iff.mp ran
      exact atomicReduction_pids _ _ _ _ _ _ _ executed
  | forLoop | forRange | forRangeDyn | forRangeInt | ifThen | ifThenElse | effectMarker =>
      simp [leafSupported] at supported

theorem Local.tick_pids (M : Algebra α) (before after : Local α) (memory : Memory α)
    (ran : before.tick M memory = some after) : after.state.pids = before.state.pids := by
  obtain ⟨code,state⟩ := before
  let shared := { state with mem := memory }
  change (Local.mk code shared).tick M shared.mem = some after at ran
  change after.state.pids = shared.pids
  cases code with
  | nil => simp [tick] at ran
  | cons command rest =>
    cases command with
    | counted index current stop body =>
      by_cases active : current < stop <;> simp [tick,active] at ran <;> subst after <;>
        rfl
    | natural index current stop stride body =>
      by_cases active : stride = 0 ∨ stop ≤ current <;> simp [tick,active] at ran <;> subst after <;>
        rfl
    | integer index current stop stride body =>
      by_cases active : stride = 0 ∨ stop ≤ current <;> simp [tick,active] at ran <;> subst after <;>
        rfl
    | source statement =>
      by_cases supported : leafSupported statement = true
      · cases advanced : step M statement shared with
        | none => simp [tick,supported,advanced] at ran
        | some next =>
          simp [tick,supported,advanced] at ran
          subst after
          exact leaf_step_pids M statement shared next supported advanced
      · have unsupported : leafSupported statement = false := Bool.eq_false_of_not_eq_true supported
        cases statement with
        | forLoop index stop body =>
          simp [tick,leafSupported] at ran
          subst after
          rfl
        | forRange index first last stride body =>
          simp [tick,leafSupported] at ran
          subst after
          rfl
        | forRangeDyn index first last stride body =>
          cases firstRead : evalOp M none first shared with
          | none => simp [tick,leafSupported,firstRead] at ran
          | some a =>
            cases lastRead : evalOp M none last shared with
            | none => simp [tick,leafSupported,firstRead,lastRead] at ran
            | some b =>
              cases strideRead : evalOp M none stride shared with
              | none => simp [tick,leafSupported,firstRead,lastRead,strideRead] at ran
              | some delta =>
                simp [tick,leafSupported,firstRead,lastRead,strideRead] at ran
                subst after
                rfl
        | forRangeInt index first last stride body =>
          cases firstRead : evalOp M none first shared with
          | none => simp [tick,leafSupported,firstRead] at ran
          | some a =>
            cases lastRead : evalOp M none last shared with
            | none => simp [tick,leafSupported,firstRead,lastRead] at ran
            | some b =>
              cases strideRead : evalOp M none stride shared with
              | none => simp [tick,leafSupported,firstRead,lastRead,strideRead] at ran
              | some delta =>
                simp [tick,leafSupported,firstRead,lastRead,strideRead] at ran
                subst after
                rfl
        | ifThen condition body =>
          cases selected : evalOp M none condition shared with
          | none => simp [tick,leafSupported,selected] at ran
          | some flag =>
            cases choice : flag () <;> simp [tick,leafSupported,selected,choice] at ran <;>
              subst after <;> rfl
        | ifThenElse condition yes no =>
          cases selected : evalOp M none condition shared with
          | none => simp [tick,leafSupported,selected] at ran
          | some flag =>
            cases choice : flag () <;> simp [tick,leafSupported,selected,choice] at ran <;>
              subst after <;> rfl
        | assign => simp [leafSupported] at unsupported
        | store => simp [leafSupported] at unsupported
        | atomicAdd => simp [tick,unsupported] at ran
        | atomicRMW => simp [tick,unsupported] at ran
        | alg => simp [tick,unsupported] at ran
        | effectMarker => simp [tick,unsupported] at ran

theorem Local.Advances.pids (M : Algebra α) {before after : Local α}
    (ran : before.Advances M after) : after.state.pids = before.state.pids := by
  induction ran with
  | refl => rfl
  | tail _ tick ih => exact (Local.tick_pids M _ _ _ tick).trans ih

theorem supported_run_pids (M : Algebra α) (body : List ComputeStmt) (initial final : State α)
    (supported : ∀ statement ∈ body, Supported statement) (ran : Structural.run M body initial = some final) :
    final.pids = initial.pids := by
  exact Local.Advances.pids M (supported_body_completes M body supported initial final ran)

theorem tick_pids (jobs : List (Invocation α)) (selected observed : Fin jobs.length)
    (before after : Configuration α jobs.length) (ran : tick jobs selected before = some after) :
    (after.locals observed).state.pids = (before.locals observed).state.pids := by
  obtain ⟨next,advanced,returned⟩ := Option.bind_eq_some_iff.mp ran
  have same := Option.some.inj returned
  subst after
  by_cases equal : observed = selected
  · subst observed
    simpa using Local.tick_pids jobs[selected].backend _ _ _ advanced
  · simp [Function.update, equal]

theorem run_pids (jobs : List (Invocation α)) (schedule : List (Fin jobs.length))
    (before after : Configuration α jobs.length) (ran : run jobs schedule before = some after)
    (observed : Fin jobs.length) :
    (after.locals observed).state.pids = (before.locals observed).state.pids := by
  induction schedule generalizing before with
  | nil => simp only [run,Option.some.injEq] at ran; subst after; rfl
  | cons selected rest ih =>
      obtain ⟨next,advanced,remaining⟩ := Option.bind_eq_some_iff.mp ran
      exact (ih next remaining).trans (tick_pids jobs selected observed before next advanced)

#axiomsClean tick_pids
#axiomsClean run_pids
#axiomsClean Local.tick_pids
#axiomsClean Local.Advances.pids
#axiomsClean supported_run_pids
#axiomsClean stepAlg_pids
#axiomsClean leaf_step_pids
#axiomsClean store_pids
#axiomsClean atomicAdd_pids
#axiomsClean atomicReduction_pids
end
end VeriTile.Triton.FP.Structural.Interleaved
