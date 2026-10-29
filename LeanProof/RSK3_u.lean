import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.Ladder1_t
import LeanProof.Ladder1_u
import LeanProof.Ladder2_t
import LeanProof.Ladder2_u
import LeanProof.RSK3_t
import Mathlib.Data.List.Sort

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option autoProp.rule false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.hashCommand false

namespace RSK

/-! # RSK algorithm — single step (proofs)

Correctness of the definitions in `RSK3_t`: the assembled rungs form a ladder
(`ladderRungs_isLadder`), the paper's Lemma 2.2 and Corollary 2.3, and the
`Ladder`-packaged step `rskStep`. The packaged definitions live here (not in
`RSK3_t`) because they bundle proofs; their computational content —
`ladderRungs` and `residual` — is trusted. -/

lemma depth_le_maxDepth (m : Multisegment) (s : Segment) (hs : s ∈ m.segments) :
    depth_of_segment m s hs ≤ maxDepth m (List.ne_nil_of_mem hs) := by
  unfold maxDepth
  exact le_maximum _ _ (List.mem_map.mpr ⟨⟨s, hs⟩, by simp, rfl⟩)

/-- The rung dominates its bucket coordinatewise, and each coordinate is attained. -/
lemma bucketRung_spec (m : Multisegment) (d : ℕ) (r : Segment)
    (h : bucketRung m d = some r) :
    (∀ x ∈ (((bucket m d).insertionSort (fun s t => subsegment (Subtype.val t) (Subtype.val s)))).map (·.val), x.a ≤ r.a ∧ x.b ≤ r.b) ∧
    (∃ x ∈ (((bucket m d).insertionSort (fun s t => subsegment (Subtype.val t) (Subtype.val s)))).map (·.val), x.a = r.a) ∧
    (∃ x ∈ (((bucket m d).insertionSort (fun s t => subsegment (Subtype.val t) (Subtype.val s)))).map (·.val), x.b = r.b) := by
  rcases hL : (((bucket m d).insertionSort (fun s t => subsegment (Subtype.val t) (Subtype.val s)))).map (·.val) with _ | ⟨s, ss⟩
  · simp [bucketRung, fiber_eq, hL] at h
  · simp only [bucketRung, fiber_eq, hL, Option.some.injEq] at h
    subst h
    rw [hL]
    refine ⟨fun x hx => ⟨?_, ?_⟩, ?_, ?_⟩
    · exact le_maximum {(x.a) | x ∈ s :: ss} (nonempty_image_cons _ _ _) ⟨x, hx, rfl⟩
    · exact le_maximum {(x.b) | x ∈ s :: ss} (nonempty_image_cons _ _ _) ⟨x, hx, rfl⟩
    · exact maximum_mem {(x.a) | x ∈ s :: ss} (nonempty_image_cons _ _ _)
    · exact maximum_mem {(x.b) | x ∈ s :: ss} (nonempty_image_cons _ _ _)

/-- Consecutive rungs are strictly `≪`: the depth-`(d+1)` rung sits below depth-`d`. -/
lemma rung_succ_ll (m : Multisegment) (d : ℕ) (r_d r_succ : Segment)
    (hr_d : bucketRung m d = some r_d)
    (hr_succ : bucketRung m (d + 1) = some r_succ) :
    r_succ ≪ r_d := by
  obtain ⟨dom_d, _, _⟩ := bucketRung_spec m d r_d hr_d
  obtain ⟨_, ⟨sa, hsa_mem, hsa⟩, ⟨sb, hsb_mem, hsb⟩⟩ := bucketRung_spec m (d + 1) r_succ hr_succ
  have key : ∀ x ∈ (((bucket m (d + 1)).insertionSort (fun s t => subsegment (Subtype.val t) (Subtype.val s)))).map (·.val), x ≪ r_d := by
    intro x hx
    obtain ⟨xs, hxs_bk, rfl⟩ := List.mem_map.mp hx
    have hxd : depth_of_segment m xs.val xs.property = d + 1 := by simpa [bucket] using hxs_bk
    obtain ⟨t, ht_in, ht_d, ht_ll⟩ := exists_pred_at_depth m d xs.val xs.property hxd
    obtain ⟨ha, hb⟩ := dom_d t (List.mem_map.mpr ⟨⟨t, ht_in⟩, by simp [bucket, ht_d], rfl⟩)
    exact ⟨lt_of_lt_of_le ht_ll.1 ha, lt_of_lt_of_le ht_ll.2 hb⟩
  exact ⟨hsa ▸ (key sa hsa_mem).1, hsb ▸ (key sb hsb_mem).2⟩

/-- A nonempty bucket yields a rung. -/
lemma bucketRung_some_of_mem (m : Multisegment) (d : ℕ) (x : Segment)
    (hx : x ∈ (((bucket m d).insertionSort (fun s t => subsegment (Subtype.val t) (Subtype.val s)))).map (·.val)) : ∃ r, bucketRung m d = some r := by
  rcases hL : (((bucket m d).insertionSort (fun s t => subsegment (Subtype.val t) (Subtype.val s)))).map (·.val) with _ | ⟨s, ss⟩
  · rw [hL] at hx; simp at hx
  · exact ⟨_, by simp only [bucketRung, fiber_eq, hL]; rfl⟩

/-- One step down: a depth-`(d+1)` rung implies a depth-`d` rung strictly above it.
The bucket below is nonempty because the head of bucket `d+1` has a predecessor at depth `d`. -/
lemma bucketRung_pred (m : Multisegment) (d : ℕ) (r : Segment)
    (hr : bucketRung m (d + 1) = some r) : ∃ r_d, bucketRung m d = some r_d ∧ r ≪ r_d := by
  rcases hL : (((bucket m (d + 1)).insertionSort (fun s t => subsegment (Subtype.val t) (Subtype.val s)))).map (·.val) with _ | ⟨s, _⟩
  · simp [bucketRung, fiber_eq, hL] at hr
  obtain ⟨xs, hxs_bk, _⟩ := List.mem_map.mp (hL ▸ List.mem_cons_self : s ∈ _)
  have hxs_d : depth_of_segment m xs.val xs.property = d + 1 := by simpa [bucket] using hxs_bk
  obtain ⟨t, ht_in, ht_d, _⟩ := exists_pred_at_depth m d xs.val xs.property hxs_d
  obtain ⟨r_d, hr_d⟩ := bucketRung_some_of_mem m d t
    (List.mem_map.mpr ⟨⟨t, ht_in⟩, by simp [bucket, ht_d], rfl⟩)
  exact ⟨r_d, hr_d, rung_succ_ll m d r_d r hr_d hr⟩

/-- Any deeper rung is strictly `≪` a shallower one — iterate `bucketRung_pred` down. -/
lemma rung_lt_ll (m : Multisegment) :
    ∀ (d : ℕ) (r : Segment), bucketRung m d = some r →
      ∀ d', d' < d → ∃ r', bucketRung m d' = some r' ∧ r ≪ r' := by
  intro d
  induction d with
  | zero => intro r _ d' hd'; exact absurd hd' (Nat.not_lt_zero d')
  | succ d ih =>
    intro r hr d' hd'
    obtain ⟨r_d, hr_d, h_succ⟩ := bucketRung_pred m d r hr
    rcases (Nat.lt_succ_iff.mp hd').lt_or_eq with hlt | heq
    · obtain ⟨r', hr', hr_d_lt⟩ := ih r_d hr_d d' hlt
      exact ⟨r', hr', ll_trans _ _ _ h_succ hr_d_lt⟩
    · subst heq; exact ⟨r_d, hr_d, h_succ⟩

lemma range_reverse_succ (n : ℕ) :
    (List.range (n + 1)).reverse = n :: (List.range n).reverse := by
  rw [List.range_succ, List.reverse_append, List.reverse_singleton]; rfl

/-- The rungs listed deepest-first are pairwise `≪`. -/
lemma pairwise_rungs (m : Multisegment) (n : ℕ) :
    ((List.range n).reverse.filterMap (bucketRung m)).Pairwise (· ≪ ·) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [range_reverse_succ]
    rcases hn : bucketRung m n with _ | r_n
    · simp only [List.filterMap_cons, hn]; exact ih
    · simp only [List.filterMap_cons, hn]
      refine List.pairwise_cons.2 ⟨fun y hy => ?_, ih⟩
      obtain ⟨d', hd'_mem, hd'_eq⟩ := List.mem_filterMap.mp hy
      obtain ⟨r', hr', hr_lt⟩ := rung_lt_ll m n r_n hn d'
        (List.mem_range.mp (List.mem_reverse.mp hd'_mem))
      rw [hd'_eq, Option.some.injEq] at hr'; subst hr'
      exact hr_lt

/-- A rung exists only if `m` is nonempty. -/
lemma ne_nil_of_bucketRung {m : Multisegment} {k : ℕ} {r : Segment}
    (h : bucketRung m k = some r) : m.segments ≠ [] :=
  List.ne_nil_of_length_pos (by have := lt_length_of_bucketRung h; omega)

/-- A rung exists only at depths `≤ maxDepth`. -/
lemma le_maxDepth_of_bucketRung {m : Multisegment} {k : ℕ} {r : Segment}
    (h : bucketRung m k = some r) : k ≤ maxDepth m (ne_nil_of_bucketRung h) := by
  obtain ⟨-, ⟨x, hx, -⟩, -⟩ := bucketRung_spec m k r h
  obtain ⟨⟨y, hy⟩, hybk, rfl⟩ := List.mem_map.mp hx
  have hd : depth_of_segment m y hy = k := by simpa [bucket] using hybk
  have := depth_le_maxDepth m y hy
  rw [hd] at this
  exact this

/-- `r ∈ 𝔩(m)` iff `r` is the rung of some fiber. -/
lemma mem_ladderRungs {m : Multisegment} {r : Segment} :
    r ∈ ladderRungs m ↔ ∃ k, bucketRung m k = some r := Iff.rfl

-- `Fintype` instances, not `Decidable` ones (the set of rungs, as `ladderRungs` and as the
-- first component of `rsk_step`): allowed in a `_u` file because any two such instances agree,
-- but they may be a little dangerous — to be checked (see TODO.md).
instance (m : Multisegment) : Fintype (ladderRungs m) :=
  inferInstanceAs (Fintype { r | ∃ k, bucketRung m k = some r })

instance (m : Multisegment) (h : m.segments ≠ []) : Fintype (rsk_step m h).1 :=
  inferInstanceAs (Fintype (ladderRungs m))

/-- The proofs work with the rungs as a list, sorted: deepest-first, it is the rungs of depth
`maxDepth`, …, `0`. -/
lemma ladderRungs_eq (m : Multisegment) (hm : m.segments ≠ []) :
    sorted (ladderRungs m) = (List.range (maxDepth m hm + 1)).reverse.filterMap (bucketRung m) := by
  have hlt : ((List.range (maxDepth m hm + 1)).reverse.filterMap (bucketRung m)).Pairwise (· < ·) :=
    (pairwise_rungs m _).imp fun {x y} h =>
      lt_of_le_of_ne ((Segment.le_def x y).mpr (Or.inl h.1)) (fun he => by
        subst he; exact lt_irrefl _ h.1)
  unfold sorted
  refine List.Perm.eq_of_pairwise (le := (· < ·)) ?_ ?_ ?_ ?_
  · intro a b _ _ h₁ h₂; exact absurd h₂ (lt_asymm h₁)
  · exact (Finset.sortedLT_sort _).pairwise
  · exact hlt
  · refine (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _)
      (hlt.imp ne_of_lt)).mpr fun r => ?_
    rw [Finset.mem_sort, Set.mem_toFinset, List.mem_filterMap]
    simp only [mem_ladderRungs, List.mem_reverse, List.mem_range]
    exact ⟨fun ⟨k, hk⟩ => ⟨k, Nat.lt_succ_of_le (le_maxDepth_of_bucketRung hk), hk⟩,
      fun ⟨k, _, hk⟩ => ⟨k, hk⟩⟩

/-- The rungs, sorted, form a ladder (pairwise `≪`). -/
lemma ladderRungs_isLadder (m : Multisegment) : isLadder (sorted (ladderRungs m)) := by
  unfold isLadder
  rw [decide_eq_true_eq]
  by_cases hm : m.segments = []
  · -- no segments, no rungs
    have : sorted (ladderRungs m) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro r hr
      obtain ⟨k, hk⟩ := mem_ladderRungs.mp (mem_sorted.mp hr)
      exact ne_nil_of_bucketRung hk hm
    rw [this]; simp
  · rw [ladderRungs_eq m hm]
    exact pairwise_rungs m _

-- /-- The extracted maximal ladder, packaged from `ladderRungs` and its proof. -/
-- def extractFullLadder (m : Multisegment) : Ladder :=
--   let l := sorted (ladderRungs m)
--   have hl : isLadder l := ladderRungs_isLadder m
--   ⟨⟨l, isLadder_sorted _ hl⟩, hl⟩

-- /-- **One step of the RSK / MW algorithm**: the extracted ladder and the residual. -/
-- def rskStep (m : Multisegment) : Ladder × Multisegment :=
--   (extractFullLadder m, residual m)

/-- A bucket element lies in `m` at depth `d`. -/
lemma mem_bucket_depth (m : Multisegment) (d : ℕ) (x : Segment)
    (hx : x ∈ (((bucket m d).insertionSort (fun s t => subsegment (Subtype.val t) (Subtype.val s)))).map (·.val)) :
    ∃ (hxm : x ∈ m.segments), depth_of_segment m x hxm = d := by
  obtain ⟨⟨y, hy⟩, hybk, rfl⟩ := List.mem_map.mp hx
  exact ⟨hy, by simp [bucket] at hybk; exact hybk⟩

/-- A depth-`d` segment of `m` lies in bucket `d`. -/
lemma mem_bucket_of_depth (m : Multisegment) (d : ℕ) (x : Segment) (hxm : x ∈ m.segments)
    (hd : depth_of_segment m x hxm = d) : x ∈ (((bucket m d).insertionSort (fun s t => subsegment (Subtype.val t) (Subtype.val s)))).map (·.val) :=
  List.mem_map.mpr ⟨⟨x, hxm⟩, by simp [bucket, hd], rfl⟩

/-- Consecutive bucket elements are nested. -/
lemma bucket_split_pair_subset (m : Multisegment) (d : ℕ) (s t : Segment)
    (l₁ l₂ : List Segment)
    (hsplit : (((bucket m d).insertionSort (fun s t => subsegment (Subtype.val t) (Subtype.val s)))).map (·.val) = l₁ ++ s :: t :: l₂) : t ⊆ s := by
  have hnested := bucket_nested m d
  rw [hsplit] at hnested
  have hp := (List.pairwise_append.mp hnested).2.1
  exact (List.pairwise_cons.mp hp).1 t (by simp)


/-- Full immediacy from an explicit consecutive split of a bucket: no other bucket
element is nested strictly between `s` and its successor `t`. -/
lemma bucket_split_immediate_nest (m : Multisegment) (d : ℕ) (s t : Segment)
    (l₁ l₂ : List Segment)
    (hsplit : (((bucket m d).insertionSort (fun s t => subsegment (Subtype.val t) (Subtype.val s)))).map (·.val) = l₁ ++ s :: t :: l₂)
    (u : Segment) (hu : u ∈ (((bucket m d).insertionSort (fun s t => subsegment (Subtype.val t) (Subtype.val s)))).map (·.val))
    (hus : u ≠ s) (hut : u ≠ t) : ¬ (u ⊆ s ∧ t ⊆ u) := by
  have hnested := bucket_nested m d
  rw [hsplit] at hu hnested
  rintro ⟨hsu, hut'⟩
  rcases List.mem_append.mp hu with hu1 | hu2
  · -- `u` is outside `s` (it comes earlier), yet nested inside it: they must be equal
    have hus' : subsegment s u := (List.pairwise_append.mp hnested).2.2 u hu1 s (by simp)
    obtain ⟨h1, h2⟩ := hsu
    obtain ⟨h3, h4⟩ := hus'
    exact hus (seg_ext (by omega) (by omega))
  · rcases List.mem_cons.mp hu2 with rfl | hu3
    · exact hus rfl
    · rcases List.mem_cons.mp hu3 with rfl | hu4
      · exact hut rfl
      · have hp := (List.pairwise_append.mp hnested).2.1
        have htu : subsegment u t := (List.pairwise_cons.mp (List.pairwise_cons.mp hp).2).1 u hu4
        obtain ⟨h1, h2⟩ := hut'
        obtain ⟨h3, h4⟩ := htu
        exact hut (seg_ext (by omega) (by omega))


/-- Lemma 2.2(1), with an explicit consecutive split instead of `bucketSucc`. -/
lemma depth_lt_between_split (m : Multisegment) (d : ℕ) (i t : Segment)
    (l₁ l₂ : List Segment)
    (hsplit : (((bucket m d).insertionSort (fun s t => subsegment (Subtype.val t) (Subtype.val s)))).map (·.val) = l₁ ++ i :: t :: l₂)
    (j : Segment) (hj : j ∈ m.segments) (htj : t ⊆ j) (hji : j ⊆ i)
    (hjnei : j ≠ i) (hjnet : j ≠ t) :
    depth_of_segment m j hj < d := by
  have hi_bk : i ∈ (((bucket m d).insertionSort (fun s t => subsegment (Subtype.val t) (Subtype.val s)))).map (·.val) := by rw [hsplit]; simp
  have ht_bk : t ∈ (((bucket m d).insertionSort (fun s t => subsegment (Subtype.val t) (Subtype.val s)))).map (·.val) := by rw [hsplit]; simp
  obtain ⟨hi_m, hi_d⟩ := mem_bucket_depth m d i hi_bk
  obtain ⟨ht_m, ht_d⟩ := mem_bucket_depth m d t ht_bk
  by_contra hge
  push_neg at hge
  rcases eq_or_lt_of_le hge with heq | hlt
  · have hjbk : j ∈ (((bucket m d).insertionSort (fun s t => subsegment (Subtype.val t) (Subtype.val s)))).map (·.val) := mem_bucket_of_depth m d j hj heq.symm
    exact bucket_split_immediate_nest m d i t l₁ l₂ hsplit j hjbk hjnei hjnet ⟨hji, htj⟩
  · obtain ⟨j', hj', hj'd, h1, h2⟩ := exists_lower_ll _ m j hj rfl d hlt
    obtain ⟨hjia, hjib⟩ := hji
    obtain ⟨htja, htjb⟩ := htj
    have hj'bk : j' ∈ (((bucket m d).insertionSort (fun s t => subsegment (Subtype.val t) (Subtype.val s)))).map (·.val) := mem_bucket_of_depth m d j' hj' hj'd
    have hj'i : j' ⊆ i := depth_subset_of_a_lt m i j' hi_m hj' (by omega) (by omega)
    have htj' : t ⊆ j' := depth_subset_of_b_lt m t j' ht_m hj' (by omega) (by omega)
    have hne_i : j' ≠ i := by rintro rfl; omega
    have hne_t : j' ≠ t := by rintro rfl; omega
    exact bucket_split_immediate_nest m d i t l₁ l₂ hsplit j' hj'bk hne_i hne_t ⟨hj'i, htj'⟩

/-- Lemma 2.2(2), with an explicit consecutive split instead of `bucketSucc`. -/
lemma lemma_2_2_2_split (m : Multisegment) (d : ℕ) (i t : Segment)
    (l₁ l₂ : List Segment)
    (hsplit : (((bucket m d).insertionSort (fun s t => subsegment (Subtype.val t) (Subtype.val s)))).map (·.val) = l₁ ++ i :: t :: l₂)
    (j : Segment) (hj : j ∈ m.segments) (ha : i.a < j.a) (hb : t.b < j.b) :
    depth_of_segment m j hj < d := by
  have hi_bk : i ∈ (((bucket m d).insertionSort (fun s t => subsegment (Subtype.val t) (Subtype.val s)))).map (·.val) := by rw [hsplit]; simp
  have ht_bk : t ∈ (((bucket m d).insertionSort (fun s t => subsegment (Subtype.val t) (Subtype.val s)))).map (·.val) := by rw [hsplit]; simp
  obtain ⟨hi_m, hi_d⟩ := mem_bucket_depth m d i hi_bk
  obtain ⟨ht_m, ht_d⟩ := mem_bucket_depth m d t ht_bk
  by_contra hnot
  push_neg at hnot
  have hji : j ⊆ i := depth_subset_of_a_lt m i j hi_m hj ha (by omega)
  have htj : t ⊆ j := depth_subset_of_b_lt m t j ht_m hj hb (by omega)
  have hjnei : j ≠ i := by rintro rfl; omega
  have hjnet : j ≠ t := by rintro rfl; omega
  have hlt := depth_lt_between_split m d i t l₁ l₂ hsplit j hj htj hji hjnei hjnet
  omega

/-- A nonempty multisegment has at least one ladder rung: the bucket of any segment's
own depth is nonempty and lies within `maxDepth`. -/
lemma ladderRungs_ne_nil (m : Multisegment) (h : m.segments ≠ []) :
    sorted (ladderRungs m) ≠ [] := by
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil m.segments h
  obtain ⟨r, hr⟩ := bucketRung_some_of_mem m (depth_of_segment m s hs) s
    (mem_bucket_of_depth m _ s hs rfl)
  apply List.ne_nil_of_mem (a := r)
  exact mem_sorted.mpr (mem_ladderRungs.mpr ⟨_, hr⟩)

end RSK

namespace RSK

seal maximum first in
/-- Membership in `bucketResidual`, unfolded: `w = [Δᵢ.a, Δᵢ₊₁.b]` for some position `i`. -/
lemma mem_bucketResidual_iff {m : Multisegment} {d : ℕ} {w : Segment} :
    w ∈ bucketResidual m d ↔
      ∃ i, ∃ _ : i + 1 < (fiber m d).length,
        w.a = (fiber m d)[i].a ∧ w.b = (fiber m d)[i + 1].b := by
  unfold bucketResidual
  simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by omega, rfl, rfl⟩
  · rintro ⟨i, hi, hwa, hwb⟩
    exact ⟨i, by omega, seg_ext hwa.symm hwb.symm⟩

/-- Every residual segment of a fiber comes from a split `fiber = l₁ ++ i :: t :: l₂`. -/
lemma bucketResidual_source {m : Multisegment} {d : ℕ} {w : Segment}
    (hw : w ∈ bucketResidual m d) :
    ∃ (i t : Segment) (l₁ l₂ : List Segment),
      fiber m d = l₁ ++ i :: t :: l₂ ∧ w.a = i.a ∧ w.b = t.b := by
  obtain ⟨j, hj, hwa, hwb⟩ := mem_bucketResidual_iff.mp hw
  refine ⟨(fiber m d)[j], (fiber m d)[j + 1], (fiber m d).take j, (fiber m d).drop (j + 2),
    ?_, hwa, hwb⟩
  conv_lhs => rw [← List.take_append_drop j (fiber m d)]
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]

seal maximum first in
/-- Conversely, every split `fiber = l₁ ++ i :: t :: l₂` contributes `[i.a, t.b]`. -/
lemma mem_bucketResidual_of_split {m : Multisegment} {d : ℕ} {i t : Segment}
    {l₁ l₂ : List Segment} (hsplit : fiber m d = l₁ ++ i :: t :: l₂) :
    ∃ w ∈ bucketResidual m d, w.a = i.a ∧ w.b = t.b := by
  have hlen : l₁.length + 1 < (fiber m d).length := by rw [hsplit]; simp
  have hi : (fiber m d)[l₁.length] = i := by
    rw [List.getElem_of_eq hsplit]; simp
  have ht : (fiber m d)[l₁.length + 1] = t := by
    rw [List.getElem_of_eq hsplit]; simp
  refine ⟨Segment (fiber m d)[l₁.length].a (fiber m d)[l₁.length + 1].b,
    mem_bucketResidual_iff.mpr ⟨l₁.length, hlen, rfl, rfl⟩, ?_, ?_⟩
  · exact (congrArg Segment.a hi :)
  · exact (congrArg Segment.b ht :)

/-- The residual's segments are the fibers' residuals, concatenated and sorted. -/
lemma residual_segments (m : Multisegment) (h : m.segments ≠ []) :
    (residual m h).segments =
      ((List.range (maxDepth m h + 1)).flatMap (fun d => bucketResidual m d)).insertionSort
        (· ≤ ·) := by
  simp [residual]

end RSK
