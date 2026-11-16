import LeanProof.Ladder2_u
import LeanProof.RSK1_t

set_option linter.style.setOption false
set_option autoProp.rule false
set_option linter.flexible false
set_option linter.style.whitespace false

/-! # RSK, part 1: proofs

`fiber m k` is exactly the bucket sorted outermost-first (`fiber_eq`): the bridge from the
paper-style definition to the proof machinery built on `sortedBucket`. -/

lemma fiber_eq (m : Multisegment) (k : ℕ) : fiber m k = (Proof.sortedBucket m k).map (·.val) := by
  unfold fiber
  rw [anyOf_eq (first_mem _ (admissibleEnumerations_nonempty m k))]
  have h := pmap_eq_sortedBucket (first_mem _ (admissibleEnumerations_nonempty m k))
    (fun _ hj => lt_length_of_mem_admissibleEnumerations (first_mem _ _) _ hj)
  rw [List.pmap_eq_map_attach] at h
  exact h

/-- A nonempty fiber has a nonempty set of begin points, and of end points: `bucketRung`
(`RSK2_t`) takes its two maxima over them. -/
lemma fiber_begins_nonempty (m : Multisegment) (d : ℕ) (h : fiber m d ≠ []) :
    Set.Nonempty {(x.a) | x ∈ fiber m d} := by
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ h
  exact ⟨s.a, s, hs, rfl⟩

lemma fiber_ends_nonempty (m : Multisegment) (d : ℕ) (h : fiber m d ≠ []) :
    Set.Nonempty {(x.b) | x ∈ fiber m d} := by
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ h
  exact ⟨s.b, s, hs, rfl⟩

-- Keyed on the fiber together with the shape of the set asked about (a `grind` pattern cannot
-- look inside the set-builder lambda), so they fire only where such a set is in question.
grind_pattern fiber_begins_nonempty => fiber m d, Set.Nonempty {(x.a) | x ∈ fiber m d}
grind_pattern fiber_ends_nonempty => fiber m d, Set.Nonempty {(x.b) | x ∈ fiber m d}
