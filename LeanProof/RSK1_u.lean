import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.Ladder1_t
import LeanProof.Ladder1_u
import LeanProof.Ladder2_t
import LeanProof.Ladder2_u
import LeanProof.RSK1_t

set_option linter.style.setOption false
set_option autoProp.rule false
set_option linter.flexible false
set_option linter.style.whitespace false

namespace RSK

/-! # RSK, part 1: proofs

`fiber m k` is exactly the bucket sorted outermost-first (`fiber_eq`): the bridge from the
paper-style definition to the proof machinery built on `sortedBucket`. -/

lemma fiber_eq (m : Multisegment) (k : ℕ) : fiber m k = (sortedBucket m k).map (·.val) := by
  unfold fiber
  rw [anyOf_eq (first_mem _ (admissibleEnumerations_nonempty m k))]
  have h := pmap_eq_sortedBucket (first_mem _ (admissibleEnumerations_nonempty m k))
    (fun _ hj => lt_length_of_mem_admissibleEnumerations (first_mem _ _) _ hj)
  rw [List.pmap_eq_map_attach] at h
  exact h

end RSK
