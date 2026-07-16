import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.Ladder_t
import LeanProof.Ladder_u
import LeanProof.RSK_t
import Mathlib.Data.List.Sort

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.hashCommand false

namespace RSK

/-! # RSK algorithm — single step (proofs)

Correctness of the definitions in `RSK_t`: the assembled rungs form a ladder
(`ladderRungs_isLadder`), the paper's Lemma 2.2 and Corollary 2.3, and the
`Ladder`-packaged step `rskStep`. The packaged definitions live here (not in
`RSK_t`) because they bundle proofs; their computational content —
`ladderRungs` and `residual` — is trusted. -/

/-- `foldl max` from any seed dominates the seed (`ℕ`). -/
lemma le_foldlMaxNat_init (l : List ℕ) (i : ℕ) : i ≤ l.foldl max i := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih => rw [List.foldl_cons]; exact le_trans (le_max_left i x) (ih (max i x))

/-- `foldl max` dominates each member (`ℕ`). -/
lemma le_foldlMaxNat_mem (l : List ℕ) (i x : ℕ) (hx : x ∈ l) : x ≤ l.foldl max i := by
  induction l generalizing i with
  | nil => simp at hx
  | cons y ys ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact le_trans (le_max_right i x) (le_foldlMaxNat_init ys (max i x))
    · exact ih (max i y) hmem

lemma depth_le_maxDepth (m : Multisegment) (s : Segment) (hs : s ∈ m.segments) :
    depth_of_segment m s hs ≤ maxDepth m := by
  unfold maxDepth
  exact le_foldlMaxNat_mem _ _ _ (List.mem_map.mpr ⟨⟨s, hs⟩, by simp⟩)

/-- The rung dominates its bucket coordinatewise, and each coordinate is attained. -/
lemma bucketRung_spec (m : Multisegment) (d : ℕ) (r : Segment)
    (h : bucketRung m d = some r) :
    (∀ x ∈ (bucket m d).map (·.val), x.a ≤ r.a ∧ x.b ≤ r.b) ∧
    (∃ x ∈ (bucket m d).map (·.val), x.a = r.a) ∧
    (∃ x ∈ (bucket m d).map (·.val), x.b = r.b) := by
  rcases hL : (bucket m d).map (·.val) with _ | ⟨s, ss⟩
  · simp [bucketRung, hL] at h
  · simp only [bucketRung, hL, Option.some.injEq] at h
    subst h
    rw [hL]
    refine ⟨fun x hx => ⟨?_, ?_⟩, ?_, ?_⟩
    · exact List.le_max_of_mem (List.mem_map_of_mem hx)
    · exact List.le_max_of_mem (List.mem_map_of_mem hx)
    · obtain ⟨x, hxmem, hxa⟩ := List.exists_of_mem_map
        (List.max_mem (by simp : (s :: ss).map (·.a) ≠ []))
      exact ⟨x, hxmem, hxa⟩
    · obtain ⟨x, hxmem, hxb⟩ := List.exists_of_mem_map
        (List.max_mem (by simp : (s :: ss).map (·.b) ≠ []))
      exact ⟨x, hxmem, hxb⟩

/-- Consecutive rungs are strictly `≪`: the depth-`(d+1)` rung sits below depth-`d`. -/
lemma rung_succ_ll (m : Multisegment) (d : ℕ) (r_d r_succ : Segment)
    (hr_d : bucketRung m d = some r_d)
    (hr_succ : bucketRung m (d + 1) = some r_succ) :
    r_succ ≪ r_d := by
  obtain ⟨dom_d, _, _⟩ := bucketRung_spec m d r_d hr_d
  obtain ⟨_, ⟨sa, hsa_mem, hsa⟩, ⟨sb, hsb_mem, hsb⟩⟩ := bucketRung_spec m (d + 1) r_succ hr_succ
  have key : ∀ x ∈ (bucket m (d + 1)).map (·.val), x ≪ r_d := by
    intro x hx
    obtain ⟨xs, hxs_bk, rfl⟩ := List.mem_map.mp hx
    have hxd : depth_of_segment m xs.val xs.property = d + 1 := by simpa [bucket] using hxs_bk
    obtain ⟨t, ht_in, ht_d, ht_ll⟩ := exists_pred_at_depth m d xs.val xs.property hxd
    obtain ⟨ha, hb⟩ := dom_d t (List.mem_map.mpr ⟨⟨t, ht_in⟩, by simp [bucket, ht_d], rfl⟩)
    exact ⟨lt_of_lt_of_le ht_ll.1 ha, lt_of_lt_of_le ht_ll.2 hb⟩
  exact ⟨hsa ▸ (key sa hsa_mem).1, hsb ▸ (key sb hsb_mem).2⟩

/-- A nonempty bucket yields a rung. -/
lemma bucketRung_some_of_mem (m : Multisegment) (d : ℕ) (x : Segment)
    (hx : x ∈ (bucket m d).map (·.val)) : ∃ r, bucketRung m d = some r := by
  rcases hL : (bucket m d).map (·.val) with _ | ⟨s, ss⟩
  · rw [hL] at hx; simp at hx
  · exact ⟨_, by simp only [bucketRung, hL]; rfl⟩

/-- One step down: a depth-`(d+1)` rung implies a depth-`d` rung strictly above it.
The bucket below is nonempty because the head of bucket `d+1` has a predecessor at depth `d`. -/
lemma bucketRung_pred (m : Multisegment) (d : ℕ) (r : Segment)
    (hr : bucketRung m (d + 1) = some r) : ∃ r_d, bucketRung m d = some r_d ∧ r ≪ r_d := by
  rcases hL : (bucket m (d + 1)).map (·.val) with _ | ⟨s, _⟩
  · simp [bucketRung, hL] at hr
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

/-- The rungs assembled by `ladderRungs` form a ladder (pairwise `≪`). -/
lemma ladderRungs_isLadder (m : Multisegment) : isLadder (ladderRungs m) := by
  unfold isLadder ladderRungs
  rw [decide_eq_true_eq]
  suffices H : ∀ n, ((List.range n).reverse.filterMap (bucketRung m)).Pairwise (· ≪ ·) from
    H (maxDepth m + 1)
  intro n
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

-- /-- The extracted maximal ladder, packaged from `ladderRungs` and its proof. -/
-- def extractFullLadder (m : Multisegment) : Ladder :=
--   let l := ladderRungs m
--   have hl : isLadder l := ladderRungs_isLadder m
--   ⟨⟨l, isLadder_sorted _ hl⟩, hl⟩

-- /-- **One step of the RSK / MW algorithm**: the extracted ladder and the residual. -/
-- def rskStep (m : Multisegment) : Ladder × Multisegment :=
--   (extractFullLadder m, residual m)

/-- A bucket element lies in `m` at depth `d`. -/
lemma mem_bucket_depth (m : Multisegment) (d : ℕ) (x : Segment)
    (hx : x ∈ (bucket m d).map (·.val)) :
    ∃ (hxm : x ∈ m.segments), depth_of_segment m x hxm = d := by
  obtain ⟨⟨y, hy⟩, hybk, rfl⟩ := List.mem_map.mp hx
  exact ⟨hy, by simp [bucket] at hybk; exact hybk⟩

/-- A depth-`d` segment of `m` lies in bucket `d`. -/
lemma mem_bucket_of_depth (m : Multisegment) (d : ℕ) (x : Segment) (hxm : x ∈ m.segments)
    (hd : depth_of_segment m x hxm = d) : x ∈ (bucket m d).map (·.val) :=
  List.mem_map.mpr ⟨⟨x, hxm⟩, by simp [bucket, hd], rfl⟩

/-- Consecutive bucket elements are nested. -/
lemma bucket_split_pair_subset (m : Multisegment) (d : ℕ) (s t : Segment)
    (l₁ l₂ : List Segment)
    (hsplit : (bucket m d).map (·.val) = l₁ ++ s :: t :: l₂) : t ⊆ s := by
  have hnested := bucket_nested m d
  rw [hsplit] at hnested
  have hp := (List.pairwise_append.mp hnested).2.1
  exact (List.pairwise_cons.mp hp).1 t (by simp)


/-- Full immediacy from an explicit consecutive split of a bucket: no other bucket
element is nested strictly between `s` and its successor `t`. -/
lemma bucket_split_immediate_nest (m : Multisegment) (d : ℕ) (s t : Segment)
    (l₁ l₂ : List Segment)
    (hsplit : (bucket m d).map (·.val) = l₁ ++ s :: t :: l₂)
    (u : Segment) (hu : u ∈ (bucket m d).map (·.val))
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
    (hsplit : (bucket m d).map (·.val) = l₁ ++ i :: t :: l₂)
    (j : Segment) (hj : j ∈ m.segments) (htj : t ⊆ j) (hji : j ⊆ i)
    (hjnei : j ≠ i) (hjnet : j ≠ t) :
    depth_of_segment m j hj < d := by
  have hi_bk : i ∈ (bucket m d).map (·.val) := by rw [hsplit]; simp
  have ht_bk : t ∈ (bucket m d).map (·.val) := by rw [hsplit]; simp
  obtain ⟨hi_m, hi_d⟩ := mem_bucket_depth m d i hi_bk
  obtain ⟨ht_m, ht_d⟩ := mem_bucket_depth m d t ht_bk
  by_contra hge
  push_neg at hge
  rcases eq_or_lt_of_le hge with heq | hlt
  · have hjbk : j ∈ (bucket m d).map (·.val) := mem_bucket_of_depth m d j hj heq.symm
    exact bucket_split_immediate_nest m d i t l₁ l₂ hsplit j hjbk hjnei hjnet ⟨hji, htj⟩
  · obtain ⟨j', hj', hj'd, h1, h2⟩ := exists_lower_ll _ m j hj rfl d hlt
    obtain ⟨hjia, hjib⟩ := hji
    obtain ⟨htja, htjb⟩ := htj
    have hj'bk : j' ∈ (bucket m d).map (·.val) := mem_bucket_of_depth m d j' hj' hj'd
    have hj'i : j' ⊆ i := depth_subset_of_a_lt m i j' hi_m hj' (by omega) (by omega)
    have htj' : t ⊆ j' := depth_subset_of_b_lt m t j' ht_m hj' (by omega) (by omega)
    have hne_i : j' ≠ i := by rintro rfl; omega
    have hne_t : j' ≠ t := by rintro rfl; omega
    exact bucket_split_immediate_nest m d i t l₁ l₂ hsplit j' hj'bk hne_i hne_t ⟨hj'i, htj'⟩

/-- Lemma 2.2(2), with an explicit consecutive split instead of `bucketSucc`. -/
lemma lemma_2_2_2_split (m : Multisegment) (d : ℕ) (i t : Segment)
    (l₁ l₂ : List Segment)
    (hsplit : (bucket m d).map (·.val) = l₁ ++ i :: t :: l₂)
    (j : Segment) (hj : j ∈ m.segments) (ha : i.a < j.a) (hb : t.b < j.b) :
    depth_of_segment m j hj < d := by
  have hi_bk : i ∈ (bucket m d).map (·.val) := by rw [hsplit]; simp
  have ht_bk : t ∈ (bucket m d).map (·.val) := by rw [hsplit]; simp
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
    ladderRungs m ≠ [] := by
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil m.segments h
  obtain ⟨r, hr⟩ := bucketRung_some_of_mem m (depth_of_segment m s hs) s
    (mem_bucket_of_depth m _ s hs rfl)
  apply List.ne_nil_of_mem (a := r)
  unfold ladderRungs
  exact List.mem_filterMap.mpr ⟨depth_of_segment m s hs,
    by rw [List.mem_reverse, List.mem_range]; exact Nat.lt_succ_of_le (depth_le_maxDepth m s hs),
    hr⟩

end RSK
