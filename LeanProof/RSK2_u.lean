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

/-! # RSK, part 2: proofs -/

/-- Consecutive segments of the fiber are nested, so `[Δᵢ.a, Δᵢ₊₁.b]` is a segment. -/
lemma fiber_a_le_succ_b (m : Multisegment) (k i : ℕ) (h : i + 1 < (fiber m k).length) :
    (fiber m k)[i].a ≤ (fiber m k)[i + 1].b := by
  have hnested : (fiber m k).Pairwise (fun s t => subsegment t s) := by
    rw [fiber_eq]; exact bucket_nested m k
  have hts : subsegment (fiber m k)[i + 1] (fiber m k)[i] :=
    List.pairwise_iff_getElem.mp hnested i (i + 1) (by omega) h (by omega)
  have := (fiber m k)[i + 1].fst_le_snd
  simp only [subsegment, Segment.a, Segment.b] at hts ⊢
  omega

-- `auto_prop` uses it for `Segment (fiber m d)[i].a (fiber m d)[i + 1].b` in `bucketResidual`:
-- keyed on the `(fiber m k)[i + 1]` term; the bound `h` it then finds by itself.
grind_pattern fiber_a_le_succ_b => (fiber m k)[i + 1]

/-- `maximum [depth_of_segment m s | s ∈ m.segments]` (`maxDepth`, in `RSK3_t`) needs that set
nonempty; it is, for `m.segments ≠ []`. Keyed on the term `m.segments` (a `grind` pattern
cannot look inside the set-builder lambda). -/
lemma depth_set_nonempty (m : Multisegment) (h : m.segments ≠ []) :
    ({x | x ∈ [depth_of_segment m s | s ∈ m.segments]} : Set ℕ).Nonempty :=
  nonempty_mem_of_ne_nil (comprehension_ne_nil _ h)
grind_pattern depth_set_nonempty => Multisegment.segments m

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
