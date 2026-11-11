import VeriTile.Triton.Float.FmaContraction

/-! Compose checked contractions beneath arbitrary application arguments.
In particular, complete reduction argument lists can be transformed without
changing their length, order, operator or reduction metadata. -/
namespace VeriTile.Triton.FP.Equational
variable {α : Type}

def FmaEdit.under (index : Nat) (edit : FmaEdit) : FmaEdit :=
  { edit with path := index :: edit.path }

theorem contractAll_append (first second : List FmaEdit) (source : Term α) :
    contractAll (first ++ second) source = (contractAll first source).bind (contractAll second) := by
  induction first generalizing source with
  | nil => rfl
  | cons edit rest ih =>
    simp only [List.cons_append,contractAll]
    cases contractAt edit.side edit.path source edit.combine <;> simp [ih]

/-- Lift an entire successful local edit sequence into one application child.
All sibling subtrees and the enclosing operation are preserved exactly. -/
theorem contractAll_under (edits : List FmaEdit) (op : Symbol) (args : List (Term α))
    (index : Nat) (inside : index < args.length) (target : Term α)
    (accepted : contractAll edits args[index] = some target) :
    contractAll (edits.map (FmaEdit.under index)) (.app op args) = some (.app op (args.set index target)) := by
  induction edits generalizing args target with
  | nil =>
    simp only [contractAll,Option.some.injEq] at accepted
    subst target
    simp [contractAll,List.set_getElem_self inside]
  | cons edit rest ih =>
    simp only [contractAll] at accepted
    cases localResult : contractAt edit.side edit.path args[index] edit.combine with
    | none => simp [localResult] at accepted
    | some changed =>
      simp only [localResult,bind,Option.bind] at accepted
      have child := ih (args.set index changed) (by simpa using inside) target
        (by simpa only [List.getElem_set_self] using accepted)
      simpa only [List.map_cons,FmaEdit.under,contractAll,contractAt,inside,dite_true,
        localResult,Option.map_some,bind,Option.bind,List.set_set] using child

/-- Process child plans in order. The offset allows the same construction
under an unchanged application prefix. -/
def childrenEdits (offset : Nat) : List (List FmaEdit) → List FmaEdit
  | [] => []
  | edits :: rest => edits.map (FmaEdit.under offset) ++ childrenEdits (offset+1) rest

structure ChildContraction (α : Type) where
  source : Term α
  target : Term α
  edits : List FmaEdit
  accepted : contractAll edits source = some target

theorem contractAll_children (op : Symbol) (before : List (Term α)) (children : List (ChildContraction α)) :
    contractAll (childrenEdits before.length (children.map ChildContraction.edits))
      (.app op (before ++ children.map ChildContraction.source)) =
      some (.app op (before ++ children.map ChildContraction.target)) := by
  induction children generalizing before with
  | nil => simp [childrenEdits,contractAll]
  | cons child rest ih =>
    have inside : before.length < (before ++ child.source :: rest.map ChildContraction.source).length := by simp
    have first := contractAll_under child.edits op (before ++ child.source :: rest.map ChildContraction.source)
      before.length inside child.target (by simpa using child.accepted)
    simp only [List.set_append_right _ _ (Nat.le_refl _),Nat.sub_self,List.set_cons_zero] at first
    simp only [List.map_cons,childrenEdits,contractAll_append,first,Option.bind_some]
    simpa only [List.length_append,List.length_singleton,List.singleton_append,List.append_assoc] using
      ih (before ++ [child.target])

def ChildContraction.keep (source : Term α) : ChildContraction α :=
  ⟨source,source,[],rfl⟩

/-- Build a checked application plan from independently checked child plans.
The numerical operator itself is unchanged, including reduction metadata. -/
def ChildContraction.app (op : Symbol) (children : List (ChildContraction α)) : ChildContraction α where
  source := .app op (children.map ChildContraction.source)
  target := .app op (children.map ChildContraction.target)
  edits := childrenEdits 0 (children.map ChildContraction.edits)
  accepted := by simpa using contractAll_children op [] children

def ChildContraction.andThen (first : ChildContraction α) (edits : List FmaEdit) (target : Term α)
    (accepted : contractAll edits first.target = some target) : ChildContraction α where
  source := first.source
  target := target
  edits := first.edits ++ edits
  accepted := by rw [contractAll_append,first.accepted]; exact accepted

theorem ChildContraction.sound (plan : ChildContraction α) : FmaContraction plan.source plan.target :=
  contractAll_sound plan.edits plan.source plan.target plan.accepted

theorem ChildContraction.inputs_perm (plan : ChildContraction α) : plan.source.inputs.Perm plan.target.inputs :=
  plan.sound.inputs_perm

#axiomsClean contractAll_append
#axiomsClean contractAll_under
#axiomsClean contractAll_children
#axiomsClean ChildContraction.app
#axiomsClean ChildContraction.andThen
#axiomsClean ChildContraction.sound
#axiomsClean ChildContraction.inputs_perm
end VeriTile.Triton.FP.Equational
