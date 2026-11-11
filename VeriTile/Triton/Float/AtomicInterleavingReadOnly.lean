import VeriTile.Triton.Float.SourceReadOnly
import VeriTile.Triton.Float.AtomicInterleavingMetadata

/-! Read-only region framing for arbitrary successful statement schedules.
The proof follows actual source control stacks, including nested loops. -/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
variable {α : Type} [Inhabited α]

def commandReadOnly (regions : RegionName → Prop) : Command → Prop
  | .source statement => readOnly regions statement
  | .counted _ _ _ body | .natural _ _ _ _ body | .integer _ _ _ _ body => readOnlyBody regions body

def pendingReadOnly (regions : RegionName → Prop) (code : List Command) : Prop :=
  ∀ command ∈ code, commandReadOnly regions command

@[simp] theorem pendingReadOnly_nil (regions : RegionName → Prop) : pendingReadOnly regions [] := by
  simp [pendingReadOnly]

@[simp] theorem pendingReadOnly_cons (regions : RegionName → Prop) (head : Command) (tail : List Command) :
    pendingReadOnly regions (head::tail) ↔ commandReadOnly regions head ∧ pendingReadOnly regions tail := by
  simp [pendingReadOnly]

@[simp] theorem pendingReadOnly_append (regions : RegionName → Prop) (first second : List Command) :
    pendingReadOnly regions (first++second) ↔ pendingReadOnly regions first ∧ pendingReadOnly regions second := by
  simp [pendingReadOnly,or_imp,forall_and]

@[simp] theorem commands_readOnly (regions : RegionName → Prop) (body : List ComputeStmt) :
    pendingReadOnly regions (commands body) ↔ readOnlyBody regions body := by
  simp [pendingReadOnly,commands,commandReadOnly,readOnlyBody_iff]

theorem Local.tick_readOnly (M : Algebra α) (regions : RegionName → Prop)
    (before after : Local α) (memory : Memory α) (confined : pendingReadOnly regions before.pending)
    (ran : before.tick M memory = some after) :
    pendingReadOnly regions after.pending ∧ (∀ region, regions region → after.state.mem region = memory region) := by
  obtain ⟨code,state⟩ := before
  let shared := { state with mem := memory }
  change (Local.mk code shared).tick M shared.mem = some after at ran
  change pendingReadOnly regions after.pending ∧ (∀ region, regions region → after.state.mem region = shared.mem region)
  change pendingReadOnly regions code at confined
  cases code with
  | nil => simp [tick] at ran
  | cons command rest =>
    have headConfined := (pendingReadOnly_cons regions command rest).mp confined |>.1
    have tailConfined := (pendingReadOnly_cons regions command rest).mp confined |>.2
    cases command with
    | counted index current stop body =>
      by_cases active : current < stop <;> simp [tick,active] at ran <;> subst after <;>
        (constructor <;> first | (intros; rfl) | simp_all [commandReadOnly,readOnly])
    | natural index current stop stride body =>
      by_cases active : stride = 0 ∨ stop ≤ current <;> simp [tick,active] at ran <;> subst after <;>
        (constructor <;> first | (intros; rfl) | simp_all [commandReadOnly,readOnly])
    | integer index current stop stride body =>
      by_cases active : stride = 0 ∨ stop ≤ current <;> simp [tick,active] at ran <;> subst after <;>
        (constructor <;> first | (intros; rfl) | simp_all [commandReadOnly,readOnly])
    | source statement =>
      by_cases supported : leafSupported statement = true
      · cases advanced : step M statement shared with
        | none => simp [tick,supported,advanced] at ran
        | some next =>
          simp [tick,supported,advanced] at ran
          subst after
          exact ⟨tailConfined,readOnly_leaf_frame M regions statement headConfined supported shared next advanced⟩
      · have unsupported : leafSupported statement = false := Bool.eq_false_of_not_eq_true supported
        cases statement with
        | forLoop index stop body =>
          simp [tick,leafSupported] at ran
          subst after
          (constructor <;> first | (intros; rfl) | simp_all [commandReadOnly,readOnly])
        | forRange index first last stride body =>
          simp [tick,leafSupported] at ran
          subst after
          (constructor <;> first | (intros; rfl) | simp_all [commandReadOnly,readOnly])
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
                (constructor <;> first | (intros; rfl) | simp_all [commandReadOnly,readOnly])
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
                (constructor <;> first | (intros; rfl) | simp_all [commandReadOnly,readOnly])
        | ifThen condition body =>
          cases selected : evalOp M none condition shared with
          | none => simp [tick,leafSupported,selected] at ran
          | some flag =>
            cases choice : flag () <;> simp [tick,leafSupported,selected,choice] at ran <;>
              subst after <;> (constructor <;> first | (intros; rfl) | simp_all [commandReadOnly,readOnly])
        | ifThenElse condition yes no =>
          cases selected : evalOp M none condition shared with
          | none => simp [tick,leafSupported,selected] at ran
          | some flag =>
            cases choice : flag () <;> simp [tick,leafSupported,selected,choice] at ran <;>
              subst after <;> (constructor <;> first | (intros; rfl) | simp_all [commandReadOnly,readOnly])
        | assign => simp [leafSupported] at unsupported
        | store => simp [leafSupported] at unsupported
        | atomicAdd => simp [tick,unsupported] at ran
        | atomicRMW => simp [tick,unsupported] at ran
        | alg => simp [tick,unsupported] at ran
        | effectMarker => simp [tick,unsupported] at ran

def Configuration.ReadOnly {count : Nat} (regions : RegionName → Prop) (state : Configuration α count) : Prop :=
  ∀ i, pendingReadOnly regions (state.locals i).pending

theorem tick_readOnly (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (selected : Fin jobs.length) (before after : Configuration α jobs.length)
    (confined : before.ReadOnly regions) (ran : tick jobs selected before = some after) :
    after.ReadOnly regions ∧ (∀ region, regions region → after.memory region = before.memory region) := by
  obtain ⟨next,advanced,returned⟩ := Option.bind_eq_some_iff.mp ran
  have same := Option.some.inj returned
  subst after
  obtain ⟨localConfined,framed⟩ := Local.tick_readOnly jobs[selected].backend regions
    (before.locals selected) next before.memory (confined selected) advanced
  refine ⟨?_,framed⟩
  intro i
  by_cases equal : i = selected
  · subst i
    simpa using localConfined
  · simpa [Function.update,equal] using confined i

theorem run_readOnly (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (schedule : List (Fin jobs.length)) (before after : Configuration α jobs.length)
    (confined : before.ReadOnly regions) (ran : run jobs schedule before = some after) :
    after.ReadOnly regions ∧ (∀ region, regions region → after.memory region = before.memory region) := by
  induction schedule generalizing before with
  | nil => simp only [run,Option.some.injEq] at ran; subst after; exact ⟨confined,fun _ _ => rfl⟩
  | cons selected rest ih =>
      obtain ⟨next,advanced,remaining⟩ := Option.bind_eq_some_iff.mp ran
      obtain ⟨nextConfined,firstFrame⟩ := tick_readOnly jobs regions selected before next confined advanced
      obtain ⟨lastConfined,restFrame⟩ := ih next nextConfined remaining
      exact ⟨lastConfined,fun region member => (restFrame region member).trans (firstFrame region member)⟩

theorem initial_readOnly (jobs : List (Invocation α)) (regions : RegionName → Prop) (state : State α)
    (confined : ∀ i : Fin jobs.length, readOnlyBody regions jobs[i].kernel.surfaceBody) :
    (initial jobs state).ReadOnly regions := by
  intro i
  change pendingReadOnly regions (match jobs[i].kernel with | .mk _ _ body => commands body)
  have source := confined i
  cases kernel : jobs[i].kernel
  simp only [kernel,ComputeKernel.surfaceBody] at source
  exact (commands_readOnly regions _).mpr source

theorem Run.readOnly (jobs : List (Invocation α)) (regions : RegionName → Prop)
    (before after : State α) (executed : Run jobs before after)
    (confined : ∀ i : Fin jobs.length, readOnlyBody regions jobs[i].kernel.surfaceBody) :
    ∀ region, regions region → after.mem region = before.mem region := by
  have framed := (run_readOnly jobs regions executed.schedule (initial jobs before) executed.result
    (initial_readOnly jobs regions before confined) executed.executed).2
  intro region member
  rw [executed.readback]
  exact framed region member

#axiomsClean tick_readOnly
#axiomsClean run_readOnly
#axiomsClean initial_readOnly
#axiomsClean Run.readOnly
#axiomsClean pendingReadOnly_nil
#axiomsClean pendingReadOnly_cons
#axiomsClean pendingReadOnly_append
#axiomsClean commands_readOnly
#axiomsClean Local.tick_readOnly
end
end VeriTile.Triton.FP.Structural.Interleaved
