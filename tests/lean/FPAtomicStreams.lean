import VeriTile.Triton.Float.OrderedStreamMerge
import VeriTile.Triton.Float.AtomicWriteStream
import VeriTile.Triton.Float.SignedLoopVisits

/-! Equal numerical operands must not erase distinct signed tile positions.
The scheduling label sequence preserves both workers' complete local order. -/
namespace FPAtomicStreamsTests
open VeriTile OrderedStreams
open Triton.FP.Structural.Interleaved

def labels (worker : Nat) : List Int := if worker = 0 then [-7,-3] else if worker = 1 then [1] else []
def history : List (Nat × Nat) := [(0,0),(1,0),(0,0)]

theorem visit_order : integerVisits (-7) 2 4 = [-7,-3,1] := by simp [integerVisits]

theorem labelled_order : merge [0,1,0] labels = some [(0,-7),(1,1),(0,-3)] := by
  simp [merge,labels,Function.update]

theorem equal_values_keep_positions :
    ∃ labelled : List (Nat × Int), merge (history.map Prod.fst) labels = some labelled ∧
      labelled.map (fun item => (item.1,0)) = history ∧
      ∀ worker, project labelled worker = labels worker := by
  apply lift history labels (fun _ _ => 0)
  intro worker
  by_cases first : worker = 0
  · subst worker; simp [history,labels,project]
  · by_cases second : worker = 1
    · subst worker; simp [history,labels,project]
    · simp [history,labels,project,first,second,Ne.symm first,Ne.symm second]

#axiomsClean visit_order
#axiomsClean labelled_order
#axiomsClean equal_values_keep_positions
end FPAtomicStreamsTests
