import VeriTile.Triton.Float.SourceReadDependency
import VeriTile.Triton.Float.AtomicInterleavingReadOnly

/-! Source read certificates follow the actual pending-control stack. -/
namespace VeriTile.Triton.FP.Structural.Interleaved
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
variable {α : Type} [Inhabited α]

def commandDependencies (regions : RegionName → Prop) : Command → Prop
  | .source statement => readDependencies regions statement
  | .counted _ _ _ body | .natural _ _ _ _ body | .integer _ _ _ _ body => bodyDependencies regions body

def pendingDependencies (regions : RegionName → Prop) (code : List Command) : Prop :=
  ∀ command ∈ code, commandDependencies regions command

@[simp] theorem pendingDependencies_nil (regions : RegionName → Prop) : pendingDependencies regions [] := by
  simp [pendingDependencies]

@[simp] theorem pendingDependencies_cons (regions : RegionName → Prop) (head : Command) (tail : List Command) :
    pendingDependencies regions (head::tail) ↔ commandDependencies regions head ∧ pendingDependencies regions tail := by
  simp [pendingDependencies]

@[simp] theorem pendingDependencies_append (regions : RegionName → Prop) (first second : List Command) :
    pendingDependencies regions (first++second) ↔ pendingDependencies regions first ∧ pendingDependencies regions second := by
  simp [pendingDependencies,or_imp,forall_and]

@[simp] theorem commands_dependencies (regions : RegionName → Prop) (body : List ComputeStmt) :
    pendingDependencies regions (commands body) ↔ bodyDependencies regions body := by
  simp [pendingDependencies,commands,commandDependencies,bodyDependencies_iff]

theorem Local.tick_dependencies (M : Algebra α) (regions : RegionName → Prop)
    (before after : Local α) (memory : Memory α) (confined : pendingDependencies regions before.pending)
    (ran : before.tick M memory = some after) :
    pendingDependencies regions after.pending := by
  obtain ⟨code,state⟩ := before
  let shared := { state with mem := memory }
  change (Local.mk code shared).tick M shared.mem = some after at ran
  change pendingDependencies regions after.pending
  change pendingDependencies regions code at confined
  cases code with
  | nil => simp [tick] at ran
  | cons command rest =>
    have headConfined := (pendingDependencies_cons regions command rest).mp confined |>.1
    have tailConfined := (pendingDependencies_cons regions command rest).mp confined |>.2
    cases command with
    | counted index current stop body =>
      by_cases active : current < stop <;> simp [tick,active] at ran <;> subst after <;>
        (simp_all [commandDependencies,readDependencies])
    | natural index current stop stride body =>
      by_cases active : stride = 0 ∨ stop ≤ current <;> simp [tick,active] at ran <;> subst after <;>
        (simp_all [commandDependencies,readDependencies])
    | integer index current stop stride body =>
      by_cases active : stride = 0 ∨ stop ≤ current <;> simp [tick,active] at ran <;> subst after <;>
        (simp_all [commandDependencies,readDependencies])
    | source statement =>
      by_cases supported : leafSupported statement = true
      · cases advanced : step M statement shared with
        | none => simp [tick,supported,advanced] at ran
        | some next =>
          simp [tick,supported,advanced] at ran
          subst after
          exact tailConfined
      · have unsupported : leafSupported statement = false := Bool.eq_false_of_not_eq_true supported
        cases statement with
        | forLoop index stop body =>
          simp [tick,leafSupported] at ran
          subst after
          (simp_all [commandDependencies,readDependencies])
        | forRange index first last stride body =>
          simp [tick,leafSupported] at ran
          subst after
          (simp_all [commandDependencies,readDependencies])
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
                (simp_all [commandDependencies,readDependencies])
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
                (simp_all [commandDependencies,readDependencies])
        | ifThen condition body =>
          cases selected : evalOp M none condition shared with
          | none => simp [tick,leafSupported,selected] at ran
          | some flag =>
            cases choice : flag () <;> simp [tick,leafSupported,selected,choice] at ran <;>
              subst after <;> (simp_all [commandDependencies,readDependencies])
        | ifThenElse condition yes no =>
          cases selected : evalOp M none condition shared with
          | none => simp [tick,leafSupported,selected] at ran
          | some flag =>
            cases choice : flag () <;> simp [tick,leafSupported,selected,choice] at ran <;>
              subst after <;> (simp_all [commandDependencies,readDependencies])
        | assign => simp [leafSupported] at unsupported
        | store => simp [leafSupported] at unsupported
        | atomicAdd => simp [tick,unsupported] at ran
        | atomicRMW => simp [tick,unsupported] at ran
        | alg => simp [tick,unsupported] at ran
        | effectMarker => simp [tick,unsupported] at ran


#axiomsClean pendingDependencies_nil
#axiomsClean pendingDependencies_cons
#axiomsClean pendingDependencies_append
#axiomsClean commands_dependencies
#axiomsClean Local.tick_dependencies
end
end VeriTile.Triton.FP.Structural.Interleaved
