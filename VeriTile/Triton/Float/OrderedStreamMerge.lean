import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Basic
import VeriTile.Meta.StatementAudit

/-! An ordered merge records only which stream supplies the next item. It
preserves every stream's order and can be replayed with different item values.
This separates scheduling choices from numerical operands. -/
namespace VeriTile.OrderedStreams
variable {ι α β : Type} [DecidableEq ι]

def project (history : List (ι × α)) (worker : ι) : List α :=
  history.filterMap (fun item => if item.1 = worker then some item.2 else none)

def merge : List ι → (ι → List α) → Option (List (ι × α))
  | [],_ => some []
  | worker :: rest,streams => do
      let item :: remaining := streams worker | none
      let tail ← merge rest (Function.update streams worker remaining)
      return (worker,item) :: tail

theorem merge_project (history : List (ι × α)) :
    merge (history.map Prod.fst) (project history) = some history := by
  induction history with
  | nil => rfl
  | cons item rest ih =>
      obtain ⟨worker,value⟩ := item
      have selected : project ((worker,value) :: rest) worker = value :: project rest worker := by simp [project]
      have remaining : Function.update (project ((worker,value) :: rest)) worker (project rest worker) = project rest := by
        funext other
        by_cases same : other = worker
        · subst other; simp
        · simp [Function.update,project,same,Ne.symm same]
      simp only [List.map_cons,merge,selected,remaining,ih]
      rfl

theorem merge_map (order : List ι) (streams : ι → List α) (value : ι → α → β) :
    merge order (fun worker => (streams worker).map (value worker)) =
      (merge order streams).map (List.map (fun item => (item.1,value item.1 item.2))) := by
  induction order generalizing streams with
  | nil => rfl
  | cons worker rest ih =>
      cases shape : streams worker with
      | nil => simp [merge,shape]
      | cons item remaining =>
          have updated : Function.update (fun worker => (streams worker).map (value worker)) worker (remaining.map (value worker)) =
              fun other => ((Function.update streams worker remaining) other).map (value other) := by
            funext other
            by_cases same : other = worker
            · subst other; simp
            · simp [Function.update,same]
          simp only [merge,shape,List.map_cons,updated,ih]
          cases merge rest (Function.update streams worker remaining) <;> rfl

theorem project_map (history : List (ι × α)) (value : ι → α → β) (worker : ι) :
    project (history.map (fun item => (item.1,value item.1 item.2))) worker =
      (project history worker).map (value worker) := by
  induction history with
  | nil => rfl
  | cons item rest ih =>
      obtain ⟨selected,item⟩ := item
      by_cases same : selected = worker
      · subst selected; simpa [project] using congrArg (List.cons (value worker item)) ih
      · simpa [project,same] using ih

theorem merge_prefix (order : List ι) (streams : ι → List α) (history : List (ι × α))
    (merged : merge order streams = some history) (worker : ι) : project history worker <+: streams worker := by
  induction order generalizing streams history with
  | nil =>
      have same : history = [] := (Option.some.inj merged).symm
      subst history
      exact List.nil_prefix
  | cons selected rest ih =>
      cases shape : streams selected with
      | nil => simp [merge,shape] at merged
      | cons item remaining =>
          simp only [merge,shape] at merged
          obtain ⟨tail,ran,same⟩ := Option.bind_eq_some_iff.mp merged
          have same := Option.some.inj same
          subst history
          have leading := ih _ tail ran
          by_cases selectedHere : selected = worker
          · subst selected
            have leading : project tail worker <+: remaining := by simpa using leading
            obtain ⟨suffix,equal⟩ := leading
            refine ⟨suffix,?_⟩
            simpa [project,shape] using congrArg (List.cons item) equal
          · have leading : project tail worker <+: streams worker := by simpa [Function.update,Ne.symm selectedHere] using leading
            simpa [project,selectedHere] using leading

/-- Recover an item-labelled merge from its values without needing the value
map to be injective. Equal numerical operands retain distinct source positions. -/
theorem lift (history : List (ι × β)) (labels : ι → List α) (value : ι → α → β)
    (streams : ∀ worker, project history worker = (labels worker).map (value worker)) :
    ∃ labelled, merge (history.map Prod.fst) labels = some labelled ∧
      labelled.map (fun item => (item.1,value item.1 item.2)) = history ∧
      ∀ worker, project labelled worker = labels worker := by
  have replay := merge_project history
  have inputs : project history = fun worker => (labels worker).map (value worker) := funext streams
  rw [inputs,merge_map] at replay
  obtain ⟨labelled,merged,values⟩ := Option.map_eq_some_iff.mp replay
  refine ⟨labelled,merged,values,?_⟩
  intro worker
  have same : (project labelled worker).map (value worker) = (labels worker).map (value worker) := by
    rw [← project_map,values,streams]
  exact (merge_prefix _ labels labelled merged worker).eq_of_length (by simpa using congrArg List.length same)

#axiomsClean merge_project
#axiomsClean merge_map
#axiomsClean project_map
#axiomsClean merge_prefix
#axiomsClean lift
end VeriTile.OrderedStreams
