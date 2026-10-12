import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.Ladder1_t
import LeanProof.Ladder1_u
import LeanProof.Ladder2_t
import LeanProof.Ladder2_u
import LeanProof.RSK1_t
import LeanProof.RSK1_u
import LeanProof.RSK2_t

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false

namespace RSK

/-! # RSK, part 2: proofs

`fiber m k` is exactly the bucket sorted outermost-first (`fiber_eq`): the bridge from the
paper-style definitions to the proof machinery built on `sortedBucket`. -/

private lemma fiber_eq_pmap (m : Multisegment) (k : ℕ) :
    fiber m k = (enumeration m k).pmap (fun j hj => m.segments[j])
      (fun _ hj => lt_length_of_mem_enumeration hj) := by
  unfold fiber
  rw [List.pmap_eq_map_attach]

/-- The fiber, in our enumeration's order, is the bucket sorted outermost-first. -/
lemma fiber_eq (m : Multisegment) (k : ℕ) : fiber m k = (sortedBucket m k).map (·.val) := by
  rw [fiber_eq_pmap]
  by_cases h : ∃ j : Fin m.segments.length, depth_of_segment m m.segments[j] = k
  · have he := enumeration_mem m k
    apply List.Perm.eq_of_pairwise (le := fun s t => subsegment t s)
    · intro a b _ _ h₁ h₂
      exact seg_ext (by simp only [subsegment] at *; omega) (by simp only [subsegment] at *; omega)
    · exact pairwise_of_mem he _
    · exact bucket_nested m k
    · exact (perm_bucket_of_mem he _).trans ((sortedBucket_perm m k).map _).symm
  · push_neg at h
    have hnil : (sortedBucket m k).map (·.val) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro s hs
      obtain ⟨⟨s, hsm⟩, hsb, rfl⟩ := List.mem_map.mp hs
      rw [mem_sortedBucket] at hsb
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hsm
      exact h ⟨j, by omega⟩ (by simpa [bucket] using hsb)
    rw [hnil]
    simp [enumeration_eq_nil h]

/-- Consecutive segments of the fiber are nested, so `[s.a, t.b]` is a segment. -/
lemma fiber_zip_a_le_b {m : Multisegment} {k : ℕ} {p : Segment × Segment}
    (hp : p ∈ (fiber m k).zip (fiber m k).tail) : p.1.a ≤ p.2.b := by
  rw [fiber_eq] at hp
  obtain ⟨l₁, l₂, hsplit⟩ := zip_tail_split _ p.1 p.2 hp
  have hnested := bucket_nested m k
  rw [hsplit] at hnested
  have hts : subsegment p.2 p.1 :=
    (List.pairwise_cons.mp (List.pairwise_append.mp hnested).2.1).1 p.2 (by simp)
  have := p.2.fst_le_snd
  simp only [subsegment, Segment.a, Segment.b] at hts ⊢
  omega

-- `auto_prop` uses it for `Segment p.1.a p.2.b` in `bucketResidual`.
macro_rules | `(tactic| auto_prop) => `(tactic| exact fiber_zip_a_le_b ‹_›)

/-- A rung exists only at the depth of some segment, so below `m.segments.length`. -/
lemma lt_length_of_bucketRung {m : Multisegment} {k : ℕ} {r : Segment}
    (h : bucketRung m k = some r) : k < m.segments.length := by
  unfold bucketRung at h
  split at h
  · exact absurd h (by simp)
  · rename_i s ss hfib
    have hs : s ∈ fiber m k := by rw [hfib]; simp
    rw [fiber_eq] at hs
    obtain ⟨⟨s, hsm⟩, hsb, rfl⟩ := List.mem_map.mp hs
    rw [mem_sortedBucket] at hsb
    have hd : depth_of_segment m s hsm = k := by simpa [bucket] using hsb
    rw [← hd]
    exact lt_length_of_mem_depthSet (depth_of_segment_mem m s hsm)

/-- The set of rungs is finite: it is computed from the depths below `m.segments.length`. -/
instance (m : Multisegment) : Fintype { r | ∃ k, bucketRung m k = some r } :=
  Fintype.ofFinset ((List.range m.segments.length).filterMap (bucketRung m)).toFinset
    (fun r => by
      simp only [List.mem_toFinset, List.mem_filterMap, List.mem_range, Set.mem_setOf_eq]
      exact ⟨fun ⟨k, _, hk⟩ => ⟨k, hk⟩, fun ⟨k, hk⟩ => ⟨k, lt_length_of_bucketRung hk, hk⟩⟩)

end RSK
