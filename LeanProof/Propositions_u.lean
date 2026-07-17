import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.Ladder_t
import LeanProof.Ladder_u
import LeanProof.RSK_t
import LeanProof.RSK_u
import LeanProof.MW_t
import LeanProof.MW_u
import LeanProof.Propositions_t

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.hashCommand false
set_option linter.style.show false

open scoped List

/-! # Machinery for `deltaCirc_eq_of_residual` (paper Prop. `lem: main2`)

Under `min m < min L(m)`, one MW step commutes with the RSK residual on the Δ°
component: `Δ°(m) = Δ°(m')`. This file proves the two halves:

* `minPreserved` — the smallest begin survives the residual (part A);
* `chainLenPreserved` — the MW leading-chain length is preserved (part B),
  by the two constructions
  - `m`-chain → boundary pairs → residual chain (`k ≤ k'`), ends increasing by
    `succ_end_mono`;
  - residual chain → `m`-chain via the paper's replacement argument (`k' ≤ k`),
    using `exists_lower_ll` when the source's end is too short.
-/

/-! ## Small order helpers -/

/-- Lex order on segments: `s ≤ t` implies `s.a ≤ t.a`. -/
lemma seg_le_imp_a_le {s t : Segment} (h : s ≤ t) : s.a ≤ t.a := by
  have h' : toLex s.toProd ≤ toLex t.toProd := h
  rw [Prod.Lex.le_iff] at h'
  rcases h' with h1 | ⟨h1, _⟩
  · exact le_of_lt h1
  · exact le_of_eq h1

/-- A list whose `head?` is `some x` is `x :: tail`. -/
lemma head?_eq_cons {α : Type*} {l : List α} {x : α} (h : l.head? = some x) :
    l = x :: l.tail := by
  cases l with
  | nil => simp at h
  | cons a t => simp only [List.head?_cons, Option.some.injEq] at h; subst h; rfl

/-- The head's begin is `≤` every segment's begin (sorted ascending). -/
lemma head_begin_le (m : Multisegment) (sₘ : Segment)
    (hsₘ : m.segments.head? = some sₘ) (s : Segment) (hs : s ∈ m.segments) :
    sₘ.a ≤ s.a := by
  have hcons := head?_eq_cons hsₘ
  apply seg_le_imp_a_le
  rw [hcons] at hs
  rcases List.mem_cons.mp hs with rfl | hmem
  · exact le_refl _
  · have hpw := m.is_sorted
    rw [hcons] at hpw
    exact (List.pairwise_cons.mp hpw).1 s hmem

/-! ## Residual membership: sources and emissions -/

/-- Every residual segment has a *source*: a position-adjacent bucket pair `(i, t)`
with `w = ⟨i.a, t.b⟩`. -/
lemma residual_source (m : Multisegment) (w : Segment) (hw : w ∈ (RSK.residual m).segments) :
    ∃ (d : ℕ) (i t : Segment) (l₁ l₂ : List Segment),
      d ≤ RSK.maxDepth m ∧ (bucket m d).map (·.val) = l₁ ++ i :: t :: l₂ ∧
      w.a = i.a ∧ w.b = t.b := by
  have hraw : w ∈ (List.range (RSK.maxDepth m + 1)).flatMap (fun d => RSK.bucketResidual m d) :=
    (List.perm_insertionSort (· ≤ ·) _).mem_iff.mp hw
  obtain ⟨d, hd, hwd⟩ := List.mem_flatMap.mp hraw
  simp only [RSK.bucketResidual] at hwd
  obtain ⟨⟨⟨i, t⟩, hpair⟩, -, hfw⟩ := List.mem_map.mp hwd
  obtain ⟨l₁, l₂, hsplit⟩ := zip_tail_split _ i t hpair
  exact ⟨d, i, t, l₁, l₂, Nat.lt_succ_iff.mp (List.mem_range.mp hd), hsplit,
    by rw [← hfw]; rfl, by rw [← hfw]; rfl⟩

/-- A residual segment of any in-range bucket lands in the residual. -/
lemma mem_residual_of_bucket (m : Multisegment) {d : ℕ} (hd : d ≤ RSK.maxDepth m)
    {w : Segment} (hw : w ∈ RSK.bucketResidual m d) : w ∈ (RSK.residual m).segments := by
  simp only [RSK.residual]
  rw [(List.perm_insertionSort (· ≤ ·) _).mem_iff]
  exact List.mem_flatMap.mpr ⟨d, List.mem_range.mpr (by omega), hw⟩

/-- Every position-adjacent bucket pair emits its derived segment `⟨i.a, t.b⟩`
into the bucket residual. -/
lemma derived_mem_bucketResidual (m : Multisegment) (d : ℕ) (i t : Segment)
    (l₁ l₂ : List Segment) (hsplit : (bucket m d).map (·.val) = l₁ ++ i :: t :: l₂) :
    ∃ w ∈ RSK.bucketResidual m d, w.a = i.a ∧ w.b = t.b := by
  have hpair : (i, t) ∈ (((bucket m d).map (·.val)).zip ((bucket m d).map (·.val)).tail) := by
    rw [hsplit]; exact mem_zip_tail_of_split l₁ i t l₂
  simp only [RSK.bucketResidual]
  exact ⟨_, List.mem_map.mpr ⟨⟨(i, t), hpair⟩, List.mem_attach _ _, rfl⟩, rfl, rfl⟩

/-- Every begin-point in the residual is `≥ min m`. -/
lemma residual_begin_ge (m : Multisegment) (sₘ : Segment)
    (hsₘ : m.segments.head? = some sₘ) (s : Segment)
    (hs : s ∈ (RSK.residual m).segments) : sₘ.a ≤ s.a := by
  obtain ⟨d, i, t, l₁, l₂, hd, hsplit, hsa, hsb⟩ := residual_source m s hs
  have hi_bk : i ∈ (bucket m d).map (·.val) := by rw [hsplit]; simp
  obtain ⟨hi_m, -⟩ := RSK.mem_bucket_depth m d i hi_bk
  have := head_begin_le m sₘ hsₘ i hi_m
  omega

/-! ## The ladder head bounds the rungs -/

/-- The ladder's head begin is `≤` any rung's begin (the ladder is pairwise `≪`,
head first). -/
lemma ladderHead_le_rung (m : Multisegment) (s_l : Segment)
    (hs_l : (RSK.ladderRungs m).head? = some s_l)
    (d : ℕ) (hd : d ≤ RSK.maxDepth m) (r : Segment) (hr : RSK.bucketRung m d = some r) :
    s_l.a ≤ r.a := by
  have hr_mem : r ∈ RSK.ladderRungs m :=
    List.mem_filterMap.mpr ⟨d, List.mem_reverse.mpr (List.mem_range.mpr (by omega)), hr⟩
  have hlad : (RSK.ladderRungs m).Pairwise (· ≪ ·) := by
    simpa [isLadder] using RSK.ladderRungs_isLadder m
  have hcons := head?_eq_cons hs_l
  rw [hcons] at hlad hr_mem
  rcases List.mem_cons.mp hr_mem with rfl | hmem
  · exact le_refl _
  · exact le_of_lt ((List.pairwise_cons.mp hlad).1 r hmem).1

/-! ## Part A: `min m = min m'` -/

/-- A bucket holding a minimal segment `p` and another with strictly larger begin is
`s0 :: s1 :: rest` (it is `a`-sorted), with the head's begin `≤ p.a`. -/
lemma bucket_sorted_cons (m : Multisegment) (d : ℕ) {p x : Segment}
    (hp : p ∈ (bucket m d).map (·.val)) (hx : x ∈ (bucket m d).map (·.val)) (hlt : p.a < x.a) :
    ∃ s0 s1 rest, (bucket m d).map (·.val) = s0 :: s1 :: rest ∧ s0.a ≤ p.a := by
  have hsorted := bucket_sorted m d
  rcases hE : (bucket m d).map (·.val) with _ | ⟨s0, _ | ⟨s1, rest⟩⟩
  · rw [hE] at hp; simp at hp
  · rw [hE] at hp hx; simp only [List.mem_singleton] at hp hx; rw [hp, hx] at hlt; omega
  · rw [hE] at hsorted hp
    refine ⟨s0, s1, rest, hE, ?_⟩
    rcases List.mem_cons.mp hp with h | h
    · exact le_of_eq (congrArg Segment.a h.symm)
    · exact (List.pairwise_cons.mp hsorted).1 p h

/-- The residual attains `min m`. This is where `min m < min L(m)` is used: at
`d₀ = depth(sₘ)` the bucket holds `sₘ` and its rung's begin is `≥ min L(m) > min m`,
so it has `≥ 2` elements and the residual's first pair begins `≤ min m`. -/
lemma residual_attains_min (m : Multisegment)
    (sₘ : Segment) (hsₘ : m.segments.head? = some sₘ)
    (s_l : Segment) (hs_l : (RSK.ladderRungs m).head? = some s_l)
    (hmin : sₘ.a < s_l.a) :
    ∃ w ∈ (RSK.residual m).segments, w.a ≤ sₘ.a := by
  have hsₘ_mem : sₘ ∈ m.segments := by rw [head?_eq_cons hsₘ]; exact List.mem_cons_self
  have hd₀le : depth_of_segment m sₘ hsₘ_mem ≤ RSK.maxDepth m :=
    RSK.depth_le_maxDepth m sₘ hsₘ_mem
  have hbk : sₘ ∈ (bucket m (depth_of_segment m sₘ hsₘ_mem)).map (·.val) :=
    RSK.mem_bucket_of_depth m _ sₘ hsₘ_mem rfl
  obtain ⟨r, hr⟩ := RSK.bucketRung_some_of_mem m _ sₘ hbk
  obtain ⟨-, ⟨xmax, hxmax, hxeq⟩, -⟩ := RSK.bucketRung_spec m _ r hr
  have hlt : sₘ.a < xmax.a := by
    have := ladderHead_le_rung m s_l hs_l _ hd₀le r hr; omega
  obtain ⟨s0, s1, rest, hseg, hs0⟩ := bucket_sorted_cons m _ hbk hxmax hlt
  obtain ⟨w, hw_mem, hwa, -⟩ :=
    derived_mem_bucketResidual m _ s0 s1 [] rest (by simpa using hseg)
  exact ⟨w, mem_residual_of_bucket m hd₀le hw_mem, by omega⟩

/-- **(A) `min m = min m'`.** The smallest begin-point survives the RSK residual. -/
lemma minPreserved
    (m : Multisegment)
    (sₘ : Segment) (hsₘ : m.segments.head? = some sₘ)
    (s_l : Segment) (hs_l : (RSK.ladderRungs m).head? = some s_l)
    (hmin : sₘ.a < s_l.a)
    (s_m' : Segment) (hs_m' : (RSK.residual m).segments.head? = some s_m') :
    s_m'.a = sₘ.a := by
  have hge : sₘ.a ≤ s_m'.a := by
    apply residual_begin_ge m sₘ hsₘ
    rw [head?_eq_cons hs_m']; exact List.mem_cons_self
  obtain ⟨w, hw_mem, hw_le⟩ := residual_attains_min m sₘ hsₘ s_l hs_l hmin
  have hle : s_m'.a ≤ w.a := by
    apply seg_le_imp_a_le
    have hcons := head?_eq_cons hs_m'
    have hpw := (RSK.residual m).is_sorted
    rw [hcons] at hpw hw_mem
    rcases List.mem_cons.mp hw_mem with rfl | hmem
    · exact le_refl _
    · exact (List.pairwise_cons.mp hpw).1 w hmem
  omega

/-! ## Structural lemmas toward `chainLenPreserved` -/

/-- Rung begins grow by at least the depth gap: the rung `n` levels shallower than depth
`d + n` has begin at least `n` larger. -/
lemma rung_a_gap (m : Multisegment) : ∀ (n d : ℕ) (r r' : Segment),
    RSK.bucketRung m d = some r → RSK.bucketRung m (d + n) = some r' → r'.a + n ≤ r.a := by
  intro n
  induction n with
  | zero =>
    intro d r r' hr hr'
    rw [Nat.add_zero] at hr'; rw [hr] at hr'
    obtain rfl := Option.some.inj hr'; simp
  | succ n ih =>
    intro d r r' hr hr'
    obtain ⟨r_mid, hmid, hll⟩ := RSK.bucketRung_pred m (d + n) r' hr'
    have hrec := ih d r r_mid hr hmid
    have := hll.1
    push_cast; omega

/-- Along an MW chain (all members of `m`), depth drops by at least the index. -/
lemma chain_depth_drop (m : Multisegment) : ∀ (l : List Segment), MW.isChain l →
    (∀ x ∈ l, x ∈ m.segments) →
    ∀ (j : ℕ) (s t : Segment) (hs : s ∈ m.segments) (ht : t ∈ m.segments),
      l[0]? = some s → l[j]? = some t →
      depth_of_segment m t ht + j ≤ depth_of_segment m s hs := by
  intro l
  induction l with
  | nil => intro _ _ j s t hs ht h0 _; simp at h0
  | cons x xs ih =>
    intro hchain hmem j s t hs ht h0 hj
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0; subst h0
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj
      have : depth_of_segment m x ht = depth_of_segment m x hs := rfl
      omega
    | succ i =>
      rw [List.getElem?_cons_succ] at hj
      rw [MW.isChain, List.isChain_cons] at hchain
      obtain ⟨hlink, htail⟩ := hchain
      cases xs with
      | nil => simp at hj
      | cons y ys =>
        have hxy : MW.chainLink x y := hlink y (by simp)
        have hy_mem : y ∈ m.segments := hmem y (by simp)
        have hdrop : depth_of_segment m y hy_mem < depth_of_segment m x hs :=
          ll_ne_depth m x y hs hy_mem hxy.1
        have hrec := ih htail (fun z hz => hmem z (by simp [hz])) i y t hy_mem ht (by simp) hj
        omega

/-- **(P1)** Every leading-chain segment is non-innermost in its bucket: its begin is
strictly below the bucket rung's. -/
lemma chain_seg_lt_rung (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a)
    (σ : Segment) (hσ : σ ∈ (MW.leadingChain m).val.segments)
    (hσm : σ ∈ m.segments)
    (r : Segment) (hr : RSK.bucketRung m (depth_of_segment m σ hσm) = some r) :
    σ.a < r.a := by
  have hsₘm : sₘ ∈ m.segments := by rw [head?_eq_cons hsₘ]; exact List.mem_cons_self
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hσ
  have h0 : (MW.leadingChain m).val.segments[0]? = some sₘ := by
    have := MW.leadingChain_head m sₘ hsₘ; rwa [List.head?_eq_getElem?] at this
  have hga : σ.a = sₘ.a + j :=
    MW.chain_get_a _ (MW.leadingChain m).property j sₘ σ h0 hj
  have hdrop : depth_of_segment m σ hσm + j ≤ depth_of_segment m sₘ hsₘm :=
    chain_depth_drop m (MW.leadingChain m).val.segments
      (MW.leadingChain m).property
      (fun x hx => MW.leadingChain_subset m x hx) j sₘ σ hsₘm hσm h0 hj
  have hsₘbk : sₘ ∈ (bucket m (depth_of_segment m sₘ hsₘm)).map (·.val) :=
    RSK.mem_bucket_of_depth m _ sₘ hsₘm rfl
  obtain ⟨r0, hr0⟩ := RSK.bucketRung_some_of_mem m _ sₘ hsₘbk
  have hslr : s_l.a ≤ r0.a :=
    ladderHead_le_rung m s_l hs_l _ (RSK.depth_le_maxDepth m sₘ hsₘm) r0 hr0
  have hgap := rung_a_gap m (depth_of_segment m sₘ hsₘm - depth_of_segment m σ hσm)
    (depth_of_segment m σ hσm) r r0 hr
    (by rw [Nat.add_sub_cancel' (by omega)]; exact hr0)
  omega

/-- In an `a`-sorted list containing an element at begin `v` and an element with begin
`> v`, there is a position-adjacent pair `(i, t)` with `i.a = v` and `v < t.a`. -/
lemma exists_boundary_split : ∀ (L : List Segment), L.Pairwise (·.a ≤ ·.a) →
    ∀ (v : ℤ), (∃ p ∈ L, p.a = v) → (∃ x ∈ L, v < x.a) →
    ∃ l₁ i t l₂, L = l₁ ++ i :: t :: l₂ ∧ i.a = v ∧ v < t.a := by
  intro L
  induction L with
  | nil => intro _ v hp _; obtain ⟨p, hp, _⟩ := hp; simp at hp
  | cons h rest ih =>
    intro hsorted v hp hx
    have hrest_sorted : rest.Pairwise (·.a ≤ ·.a) := (List.pairwise_cons.mp hsorted).2
    have hha : ∀ y ∈ rest, h.a ≤ y.a := (List.pairwise_cons.mp hsorted).1
    obtain ⟨p, hpmem, hpv⟩ := hp
    have hhav : h.a ≤ v := by
      rcases List.mem_cons.mp hpmem with rfl | hpr
      · exact le_of_eq hpv
      · exact le_trans (hha p hpr) (le_of_eq hpv)
    obtain ⟨x, hxmem, hxv⟩ := hx
    by_cases hhv : h.a = v
    · by_cases hrestv : ∃ p' ∈ rest, p'.a = v
      · have hxrest : ∃ x ∈ rest, v < x.a := by
          rcases List.mem_cons.mp hxmem with rfl | hxr
          · exact absurd hxv (by rw [hhv]; exact lt_irrefl v)
          · exact ⟨x, hxr, hxv⟩
        obtain ⟨l₁, i, t, l₂, heq, hia, hta⟩ := ih hrest_sorted v hrestv hxrest
        exact ⟨h :: l₁, i, t, l₂, by rw [heq]; rfl, hia, hta⟩
      · push_neg at hrestv
        have hxrest : x ∈ rest := by
          rcases List.mem_cons.mp hxmem with rfl | hxr
          · exact absurd hxv (by rw [hhv]; exact lt_irrefl v)
          · exact hxr
        cases rest with
        | nil => simp at hxrest
        | cons r rs =>
          have hra : v < r.a := by
            have h1 := hha r (by simp)
            have hrv : r.a ≠ v := fun hh => hrestv r (by simp) hh
            omega
          exact ⟨[], h, r, rs, rfl, hhv, hra⟩
    · have hha_lt : h.a < v := lt_of_le_of_ne hhav hhv
      have hprest : ∃ p ∈ rest, p.a = v := by
        rcases List.mem_cons.mp hpmem with rfl | hpr
        · exact absurd hpv (by omega)
        · exact ⟨p, hpr, hpv⟩
      have hxrest : ∃ x ∈ rest, v < x.a := by
        rcases List.mem_cons.mp hxmem with rfl | hxr
        · exact absurd hxv (by omega)
        · exact ⟨x, hxr, hxv⟩
      obtain ⟨l₁, i, t, l₂, heq, hia, hta⟩ := ih hrest_sorted v hprest hxrest
      exact ⟨h :: l₁, i, t, l₂, by rw [heq]; rfl, hia, hta⟩

/-- Each leading-chain segment `σ` yields a *boundary pair* in its depth bucket: a
position-adjacent `(i, t)` with `i.a = σ.a` and `σ.a < t.a`. -/
lemma chain_seg_boundary (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a)
    (σ : Segment) (hσ : σ ∈ (MW.leadingChain m).val.segments)
    (hσm : σ ∈ m.segments) :
    ∃ l₁ i t l₂, (bucket m (depth_of_segment m σ hσm)).map (·.val) = l₁ ++ i :: t :: l₂
      ∧ i.a = σ.a ∧ σ.a < t.a := by
  have hσbk : σ ∈ (bucket m (depth_of_segment m σ hσm)).map (·.val) :=
    RSK.mem_bucket_of_depth m _ σ hσm rfl
  obtain ⟨r, hr⟩ := RSK.bucketRung_some_of_mem m _ σ hσbk
  have hlt : σ.a < r.a := chain_seg_lt_rung m sₘ s_l hsₘ hs_l hmin σ hσ hσm r hr
  obtain ⟨-, ⟨xmax, hxmax, hxeq⟩, -⟩ := RSK.bucketRung_spec m _ r hr
  exact exists_boundary_split _ (bucket_sorted m _) σ.a ⟨σ, hσbk, rfl⟩ ⟨xmax, hxmax, by omega⟩

/-- **End-monotonicity of the residual construction.** For position-adjacent bucket
pairs `(i, t)` at depth `d` and `(i', t')` at depth `d' < d`, if `i'.a ≤ t.a` then
`t.b < t'.b` — the residual-chain ends strictly increase. -/
lemma succ_end_mono (m : Multisegment) (i i' t t' : Segment)
    (hi : i ∈ m.segments) (hi' : i' ∈ m.segments)
    (l1 l2 : List Segment)
    (hsp : (bucket m (depth_of_segment m i hi)).map (·.val) = l1 ++ i :: t :: l2)
    (l1' l2' : List Segment)
    (hsp' : (bucket m (depth_of_segment m i' hi')).map (·.val) = l1' ++ i' :: t' :: l2')
    (hdd : depth_of_segment m i' hi' < depth_of_segment m i hi)
    (hai : i'.a ≤ t.a) :
    t.b < t'.b := by
  have ht_bk : t ∈ (bucket m (depth_of_segment m i hi)).map (·.val) := by rw [hsp]; simp
  obtain ⟨htm, htd⟩ := RSK.mem_bucket_depth m (depth_of_segment m i hi) t ht_bk
  have ht'_bk : t' ∈ (bucket m (depth_of_segment m i' hi')).map (·.val) := by rw [hsp']; simp
  obtain ⟨ht'm, ht'd⟩ := RSK.mem_bucket_depth m (depth_of_segment m i' hi') t' ht'_bk
  have h_t_sub_i' : t ⊆ i' :=
    depth_subset_of_a_le m i' t hi' htm hai (by rw [htd]; exact hdd)
  by_contra hcon
  push_neg at hcon
  have h_t'_sub_t : t' ⊆ t :=
    depth_subset_of_b_le m t' t ht'm htm hcon (by rw [htd, ht'd]; exact hdd)
  have htne_i' : t ≠ i' := by
    rintro rfl
    have : depth_of_segment m t hi' = depth_of_segment m t htm := rfl
    omega
  have htne_t' : t ≠ t' := by
    rintro rfl
    have : depth_of_segment m t ht'm = depth_of_segment m t htm := rfl
    omega
  have hlt := RSK.depth_lt_between_split m (depth_of_segment m i' hi') i' t' l1' l2' hsp' t htm
    h_t'_sub_t h_t_sub_i' htne_i' htne_t'
  rw [htd] at hlt
  omega

/-! ## Part B, forward direction: `k ≤ k'` -/

/-- From a sub-chain of `m`'s leading chain, construct an MW-chain of the same length in
the residual: each segment's boundary pair emits a derived segment, and the ends strictly
increase by `succ_end_mono`. The head data is exposed for the chain-link induction. -/
lemma forward_chain (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a) :
    ∀ (l : List Segment), (∀ σ ∈ l, σ ∈ (MW.leadingChain m).val.segments) → MW.isChain l →
    ∃ c : List Segment, MW.isChain c ∧ c.length = l.length ∧
      (∀ w ∈ c, w ∈ (RSK.residual m).segments) ∧
      (∀ σ0 ∈ l.head?, ∃ (hσ0m : σ0 ∈ m.segments) (i t : Segment) (l₁ l₂ : List Segment),
        (bucket m (depth_of_segment m σ0 hσ0m)).map (·.val) = l₁ ++ i :: t :: l₂ ∧
        i.a = σ0.a ∧ σ0.a < t.a ∧
        ∃ w0 ∈ c.head?, w0.a = σ0.a ∧ w0.b = t.b) := by
  intro l
  induction l with
  | nil => intro _ _; exact ⟨[], by simp [MW.isChain], rfl, by simp, by simp⟩
  | cons σ l' ih =>
    intro hmem hchain
    have hσ_lc : σ ∈ (MW.leadingChain m).val.segments := hmem σ (by simp)
    have hσm : σ ∈ m.segments := MW.leadingChain_subset m σ hσ_lc
    obtain ⟨l₁, i, t, l₂, hsplit, hia, hta⟩ :=
      chain_seg_boundary m sₘ s_l hsₘ hs_l hmin σ hσ_lc hσm
    obtain ⟨w, hw_bres, hwa, hwb⟩ := derived_mem_bucketResidual m _ i t l₁ l₂ hsplit
    have hw_res : w ∈ (RSK.residual m).segments :=
      mem_residual_of_bucket m (RSK.depth_le_maxDepth m σ hσm) hw_bres
    have hchain' : MW.isChain l' := by
      rw [MW.isChain, List.isChain_cons] at hchain; exact hchain.2
    obtain ⟨c', hc'chain, hc'len, hc'mem, hc'head⟩ :=
      ih (fun x hx => hmem x (by simp [hx])) hchain'
    refine ⟨w :: c', ?_, by simp [hc'len], ?_, ?_⟩
    · -- the constructed list is an MW-chain
      rw [MW.isChain, List.isChain_cons]
      refine ⟨?_, hc'chain⟩
      intro y hy
      cases hl' : l' with
      | nil =>
        rw [hl'] at hc'len
        cases c' with
        | nil => simp at hy
        | cons z zs => simp at hc'len
      | cons σ' l'' =>
        obtain ⟨hσ'm, i', t', l₁', l₂', hsplit', hia', hta', w0', hw0'head, hw0'a, hw0'b⟩ :=
          hc'head σ' (by rw [hl']; simp)
        have hy_eq : y = w0' := by
          rw [Option.mem_def] at hy hw0'head
          rw [hy] at hw0'head
          exact Option.some.inj hw0'head
        subst hy_eq
        have hlink_σ : MW.chainLink σ σ' := by
          rw [MW.isChain, List.isChain_cons] at hchain
          exact hchain.1 σ' (by rw [hl']; simp)
        have hi_bk : i ∈ (bucket m (depth_of_segment m σ hσm)).map (·.val) := by
          rw [hsplit]; simp
        obtain ⟨hi_m, hi_d⟩ := RSK.mem_bucket_depth m _ i hi_bk
        have hi'_bk : i' ∈ (bucket m (depth_of_segment m σ' hσ'm)).map (·.val) := by
          rw [hsplit']; simp
        obtain ⟨hi'_m, hi'_d⟩ := RSK.mem_bucket_depth m _ i' hi'_bk
        have hdd : depth_of_segment m σ' hσ'm < depth_of_segment m σ hσm :=
          ll_ne_depth m σ σ' hσm hσ'm hlink_σ.1
        have hsp : (bucket m (depth_of_segment m i hi_m)).map (·.val)
            = l₁ ++ i :: t :: l₂ := by rw [hi_d]; exact hsplit
        have hsp' : (bucket m (depth_of_segment m i' hi'_m)).map (·.val)
            = l₁' ++ i' :: t' :: l₂' := by rw [hi'_d]; exact hsplit'
        have hdd' : depth_of_segment m i' hi'_m < depth_of_segment m i hi_m := by
          rw [hi_d, hi'_d]; exact hdd
        have hai : i'.a ≤ t.a := by
          have h1 : σ'.a = σ.a + 1 := hlink_σ.2
          omega
        have hend := succ_end_mono m i i' t t' hi_m hi'_m l₁ l₂ hsp l₁' l₂' hsp' hdd' hai
        have h1 : σ'.a = σ.a + 1 := hlink_σ.2
        exact ⟨⟨by omega, by omega⟩, by omega⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hxc
      · exact hw_res
      · exact hc'mem x hxc
    · intro σ0 hσ0
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hσ0
      subst hσ0
      exact ⟨hσm, i, t, l₁, l₂, hsplit, hia, hta, w, by simp, hwa.trans hia, hwb⟩


/-- If the minimum of `m` begins strictly before the minimum ladder rung, the RSK
residual is nonempty. Otherwise every bucket would be a singleton — in particular the
bucket of the head's own depth would be `[head]`, making the head itself a ladder rung;
but every rung begins at or after the first rung, contradicting `h_min`. -/
lemma cond_rsk_residual_nonempty
    (m : Multisegment) (h : m.segments ≠ []) (h_min : min_m_lt_min_lm m h) :
    (RSK.residual m).segments ≠ [] := by
  intro hres
  have hs_mem : m.segments.head h ∈ m.segments := List.head_mem h
  -- the flattened raw residuals are empty
  have hraw : (List.range (RSK.maxDepth m + 1)).flatMap (fun d => RSK.bucketResidual m d)
      = [] := by
    have hperm : (RSK.residual m).segments.Perm
        ((List.range (RSK.maxDepth m + 1)).flatMap (fun d => RSK.bucketResidual m d)) :=
      List.perm_insertionSort _ _
    rw [hres] at hperm
    exact hperm.symm.eq_nil
  have hd0_range : depth_of_segment m (m.segments.head h) hs_mem ∈
      List.range (RSK.maxDepth m + 1) :=
    List.mem_range.mpr (Nat.lt_succ_of_le (RSK.depth_le_maxDepth m _ hs_mem))
  have hbres : RSK.bucketResidual m (depth_of_segment m (m.segments.head h) hs_mem) = [] :=
    List.flatMap_eq_nil_iff.mp hraw _ hd0_range
  -- the head's bucket, being residual-free, is the singleton [head]
  have hbk : m.segments.head h ∈
      (bucket m (depth_of_segment m (m.segments.head h) hs_mem)).map (·.val) :=
    RSK.mem_bucket_of_depth m _ _ hs_mem rfl
  have hsegs : (bucket m (depth_of_segment m (m.segments.head h) hs_mem)).map (·.val)
      = [m.segments.head h] := by
    rcases hL : (bucket m (depth_of_segment m (m.segments.head h) hs_mem)).map (·.val)
      with _ | ⟨s, rest⟩
    · rw [hL] at hbk; simp at hbk
    · rcases rest with _ | ⟨t, rest'⟩
      · rw [hL] at hbk
        simp only [List.mem_singleton] at hbk
        rw [hL, hbk]
      · exfalso
        apply absurd hbres
        simp only [RSK.bucketResidual]
        intro hc
        have hlen := congrArg List.length hc
        have hlen2 := congrArg List.length hL
        simp at hlen hlen2
        omega
  -- its rung exists and attains the head's begin point
  obtain ⟨r, hr⟩ := RSK.bucketRung_some_of_mem m _ _ hbk
  obtain ⟨-, ⟨x, hx_mem, hxa⟩, -⟩ := RSK.bucketRung_spec m _ r hr
  rw [hsegs] at hx_mem
  simp only [List.mem_singleton] at hx_mem
  subst hx_mem
  -- so the head's begin is a rung's begin
  have hr_mem : r ∈ RSK.ladderRungs m := by
    unfold RSK.ladderRungs
    exact List.mem_filterMap.mpr ⟨_, by rwa [List.mem_reverse], hr⟩
  -- but the first rung begins weakly before every rung — contradiction with `h_min`
  have hne_lr : RSK.ladderRungs m ≠ [] := List.ne_nil_of_mem hr_mem
  have h_min' : (m.segments.head h).a < ((RSK.ladderRungs m).head hne_lr).a := h_min
  have hpw : (RSK.ladderRungs m).Pairwise (· ≪ ·) := by
    simpa [isLadder] using RSK.ladderRungs_isLadder m
  rcases hLR : RSK.ladderRungs m with _ | ⟨hd, tl⟩
  · exact hne_lr hLR
  · have h1 := List.head?_eq_some_head hne_lr
    rw (occs := .pos [1]) [hLR] at h1
    simp only [List.head?_cons, Option.some.injEq] at h1
    rw [← h1] at h_min'
    rw [hLR] at hpw hr_mem
    rcases List.mem_cons.mp hr_mem with heq | hmem_tl
    · rw [heq] at hxa
      omega
    · have hlt : hd.a < r.a := ((List.pairwise_cons.mp hpw).1 r hmem_tl).1
      omega




/-- **Forward inequality**: the MW leading chain of `m` is no longer than that of the
residual. -/
lemma forward_len (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a)
    (s_m' : Segment) (hs_m' : (RSK.residual m).segments.head? = some s_m') :
    (MW.leadingChain m).val.segments.length
      ≤ (MW.leadingChain (RSK.residual m)).val.segments.length := by
  obtain ⟨c, hc_chain, hc_len, hc_mem, hc_head⟩ :=
    forward_chain m sₘ s_l hsₘ hs_l hmin (MW.leadingChain m).val.segments
      (fun _ hx => hx) (MW.leadingChain m).property
  rw [← hc_len]
  apply MW.leadingChain_length_ge'' (RSK.residual m) c s_m' hc_chain hc_mem hs_m'
  intro x hx
  have hlc_head := MW.leadingChain_head m sₘ hsₘ
  obtain ⟨hσ0m, i, t, l₁, l₂, -, -, -, w0, hw0_head, hw0a, -⟩ :=
    hc_head sₘ (by rw [Option.mem_def]; exact hlc_head)
  rw [Option.mem_def, hx] at hw0_head
  obtain rfl := Option.some.inj hw0_head
  rw [minPreserved m sₘ hsₘ s_l hs_l hmin s_m' hs_m']
  exact hw0a

/-! ## Part B, reverse direction: `k' ≤ k` -/

/-- **Pullback of a residual chain into `m`** (the paper's replacement argument,
Prop. main2(b)/(c)). Walking along an MW-chain of the residual with state `x ∈ m`
satisfying `x.a = w.a`, `w.b ≤ x.b`, `d ≤ depth x` (`d` a source depth of `w`):
the next residual element `w'` pulls back to `x'` — either its own source-outer `i'`
(if that extends `x`), or a replacement from `exists_lower_ll` at the strictly smaller
source depth `d' < d` (Corollary 2.3). -/
lemma pullback_go (m : Multisegment) :
    ∀ (l : List Segment) (w x : Segment) (d : ℕ),
      (∃ (i t : Segment) (l₁ l₂ : List Segment),
        (bucket m d).map (·.val) = l₁ ++ i :: t :: l₂ ∧ w.a = i.a ∧ w.b = t.b) →
      ∀ (hx : x ∈ m.segments), x.a = w.a → w.b ≤ x.b → d ≤ depth_of_segment m x hx →
      MW.isChain (w :: l) → (∀ u ∈ w :: l, u ∈ (RSK.residual m).segments) →
      ∃ c : List Segment, MW.isChain (x :: c) ∧ c.length = l.length ∧
        (∀ y ∈ x :: c, y ∈ m.segments) := by
  intro l
  induction l with
  | nil =>
    intro w x d _ hx _ _ _ _ _
    refine ⟨[], by simp [MW.isChain], rfl, ?_⟩
    intro y hy; simp only [List.mem_singleton] at hy; subst hy; exact hx
  | cons w' l' ih =>
    intro w x d hsrc hx hxa hwbx hdx hchain hmem
    obtain ⟨i, t, l₁, l₂, hsplit, hwa, hwb⟩ := hsrc
    have hw'_res : w' ∈ (RSK.residual m).segments := hmem w' (by simp)
    obtain ⟨d', i', t', l₁', l₂', hd'le, hsplit', hw'a, hw'b⟩ := residual_source m w' hw'_res
    have hlink : MW.chainLink w w' := by
      rw [MW.isChain, List.isChain_cons] at hchain
      exact hchain.1 w' (by simp)
    have ht'i' : t' ⊆ i' := RSK.bucket_split_pair_subset m d' i' t' l₁' l₂' hsplit'
    obtain ⟨ht'i'a, ht'i'b⟩ := ht'i'
    have hi'_bk : i' ∈ (bucket m d').map (·.val) := by rw [hsplit']; simp
    obtain ⟨hi'_m, hi'_d⟩ := RSK.mem_bucket_depth m d' i' hi'_bk
    have hwlt_a : w.a < w'.a := hlink.1.1
    have hwlt_b : w.b < w'.b := hlink.1.2
    have hw'a1 : w'.a = w.a + 1 := hlink.2
    -- Corollary 2.3: the source depths strictly drop
    have hd'd : d' < d := by
      have hdrop := RSK.lemma_2_2_2_split m d i t l₁ l₂ hsplit i' hi'_m
        (by omega) (by omega)
      omega
    have hchain_tail : MW.isChain (w' :: l') := by
      rw [MW.isChain, List.isChain_cons] at hchain; exact hchain.2
    have hmem_tail : ∀ u ∈ w' :: l', u ∈ (RSK.residual m).segments := by
      intro u hu; exact hmem u (by simp [hu])
    by_cases hcase : x.b < i'.b
    · -- take x' := i' itself
      obtain ⟨c', hc'_chain, hc'_len, hc'_mem⟩ := ih w' i' d'
        ⟨i', t', l₁', l₂', hsplit', hw'a, hw'b⟩ hi'_m hw'a.symm (by omega)
        (le_of_eq hi'_d.symm) hchain_tail hmem_tail
      refine ⟨i' :: c', ?_, by simpa using hc'_len, ?_⟩
      · rw [MW.isChain, List.isChain_cons]
        refine ⟨?_, hc'_chain⟩
        intro y hy
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        subst hy
        exact ⟨⟨by omega, hcase⟩, by omega⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hyc
        · exact hx
        · exact hc'_mem y hyc
    · -- replacement: `exists_lower_ll` supplies x' at depth d' with x ≪ x'
      push_neg at hcase
      have hdx' : d' < depth_of_segment m x hx := by omega
      obtain ⟨x', hx'm, hx'd, hxx'⟩ :=
        exists_lower_ll (depth_of_segment m x hx) m x hx rfl d' hdx'
      obtain ⟨hxx'a, hxx'b⟩ := hxx'
      have hx'a : x'.a = x.a + 1 := by
        by_contra hne
        have hia' : i' ≪ x' := ⟨by omega, by omega⟩
        have := ll_ne_depth m i' x' hi'_m hx'm hia'
        omega
      obtain ⟨c', hc'_chain, hc'_len, hc'_mem⟩ := ih w' x' d'
        ⟨i', t', l₁', l₂', hsplit', hw'a, hw'b⟩ hx'm (by omega) (by omega)
        (le_of_eq hx'd.symm) hchain_tail hmem_tail
      refine ⟨x' :: c', ?_, by simpa using hc'_len, ?_⟩
      · rw [MW.isChain, List.isChain_cons]
        refine ⟨?_, hc'_chain⟩
        intro y hy
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        subst hy
        exact ⟨⟨hxx'a, hxx'b⟩, by omega⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hyc
        · exact hx
        · exact hc'_mem y hyc

/-- **Reverse inequality**: the MW leading chain of the residual is no longer than that
of `m`. -/
lemma reverse_len (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a) :
    (MW.leadingChain (RSK.residual m)).val.segments.length
      ≤ (MW.leadingChain m).val.segments.length := by
  rcases hLC' : (MW.leadingChain (RSK.residual m)).val.segments with _ | ⟨w0, rest⟩
  · simp
  · have hw0_res : w0 ∈ (RSK.residual m).segments :=
      MW.leadingChain_subset (RSK.residual m) w0 (by rw [hLC']; simp)
    obtain ⟨d0, i0, t0, l₁0, l₂0, hd0le, hsplit0, hw0a, hw0b⟩ := residual_source m w0 hw0_res
    have hi0_bk : i0 ∈ (bucket m d0).map (·.val) := by rw [hsplit0]; simp
    obtain ⟨hi0_m, hi0_d⟩ := RSK.mem_bucket_depth m d0 i0 hi0_bk
    obtain ⟨ht0a, ht0b⟩ := RSK.bucket_split_pair_subset m d0 i0 t0 l₁0 l₂0 hsplit0
    have hchainLC : MW.isChain (w0 :: rest) := by
      rw [← hLC']; exact (MW.leadingChain (RSK.residual m)).property
    have hmemLC : ∀ u ∈ w0 :: rest, u ∈ (RSK.residual m).segments := by
      intro u hu; rw [← hLC'] at hu; exact MW.leadingChain_subset _ u hu
    obtain ⟨c, hc_chain, hc_len, hc_mem⟩ := pullback_go m rest w0 i0 d0
      ⟨i0, t0, l₁0, l₂0, hsplit0, hw0a, hw0b⟩ hi0_m hw0a.symm (by omega)
      (le_of_eq hi0_d.symm) hchainLC hmemLC
    -- the residual is nonempty; its head begins at `min m`
    have hne : (RSK.residual m).segments ≠ [] := List.ne_nil_of_mem hw0_res
    obtain ⟨s_m', tl', hcons'⟩ := List.exists_cons_of_ne_nil hne
    have hs_m' : (RSK.residual m).segments.head? = some s_m' := by rw [hcons']; rfl
    have hw0_head : (MW.leadingChain (RSK.residual m)).val.segments.head? = some s_m' :=
      MW.leadingChain_head (RSK.residual m) s_m' hs_m'
    rw [hLC'] at hw0_head
    simp only [List.head?_cons, Option.some.injEq] at hw0_head
    have hbound := MW.leadingChain_length_ge'' m (i0 :: c) sₘ hc_chain hc_mem hsₘ ?_
    · simpa [hc_len] using hbound
    · intro y hy
      simp only [List.head?_cons, Option.some.injEq] at hy
      subst hy
      have h1 : s_m'.a = sₘ.a := minPreserved m sₘ hsₘ s_l hs_l hmin s_m' hs_m'
      rw [hw0_head] at hw0a
      omega

/-- **(B) The MW leading-chain length is preserved by the RSK residual.** -/
lemma chainLenPreserved (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a) :
    (MW.leadingChain (RSK.residual m)).val.segments.length
      = (MW.leadingChain m).val.segments.length := by
  obtain ⟨w, hw, -⟩ := residual_attains_min m sₘ hsₘ s_l hs_l hmin
  have hne : (RSK.residual m).segments ≠ [] := List.ne_nil_of_mem hw
  obtain ⟨s_m', tl, hcons⟩ := List.exists_cons_of_ne_nil hne
  have hs_m' : (RSK.residual m).segments.head? = some s_m' := by rw [hcons]; rfl
  exact le_antisymm (reverse_len m sₘ s_l hsₘ hs_l hmin)
    (forward_len m sₘ s_l hsₘ hs_l hmin s_m' hs_m')

/-! ## Bridging `MW.mw_step` to `MW.leadingChain` -/

/-- The greedy scan skips the head itself (`¬ chainLink first first`). -/
lemma go_cons_self (first : Segment) (rest : List Segment) :
    MW.extendChain.go (first :: rest) [first] (by simp) =
      MW.extendChain.go rest [first] (by simp) := by
  rw [MW.extendChain.go]
  rw [dif_neg]
  intro h
  exact absurd h.1.1 (lt_irrefl first.a)

/-- `leadingChain` is the greedy scan of the tail from the singleton head chain. -/
lemma leadingChain_eq_go (m : Multisegment) (first : Segment) (rest : List Segment)
    (hseg : m.segments = first :: rest) :
    (MW.leadingChain m).val.segments = MW.extendChain.go rest [first] (by simp) := by
  unfold MW.leadingChain
  split
  · rename_i heq
    rw [hseg] at heq
    simp at heq
  · rename_i f r heq
    rw [hseg] at heq
    obtain ⟨rfl, rfl⟩ := List.cons.inj heq
    rfl

/-- The chain scanned by `mw_step` (full list from the singleton head) is exactly the
leading chain. -/
lemma go_full_eq (m : Multisegment) (x : Segment) (hx : m.segments.head? = some x)
    (hne : [x] ≠ []) :
    MW.extendChain.go m.segments [x] hne = (MW.leadingChain m).val.segments := by
  have hseg := head?_eq_cons hx
  rw [hseg, go_cons_self x m.segments.tail, leadingChain_eq_go m x m.segments.tail hseg]

/-- The Δ° outputs of `mw_step` agree whenever the head begins and the leading-chain
lengths agree. -/
lemma mw_step_fst_eq (m m' : Multisegment) (hm : m.segments ≠ []) (hm' : m'.segments ≠ [])
    (ha : (m'.segments.head hm').a = (m.segments.head hm).a)
    (hk : (MW.leadingChain m').val.segments.length
        = (MW.leadingChain m).val.segments.length) :
    (MW.mw_step m hm).1 = (MW.mw_step m' hm').1 := by
  apply seg_ext
  · show (m.segments.head hm).a = (m'.segments.head hm').a
    exact ha.symm
  · show (m.segments.head hm).a
        + ↑((MW.extendChain.go m.segments [m.segments.head hm] (by simp)).length - 1)
      = (m'.segments.head hm').a
        + ↑((MW.extendChain.go m'.segments [m'.segments.head hm'] (by simp)).length - 1)
    rw [go_full_eq m _ (List.head?_eq_some_head hm) (by simp),
      go_full_eq m' _ (List.head?_eq_some_head hm') (by simp), ha, hk]
/-! # Machinery for `mw_preserves_ladder` (paper Lemma `pre1` + Prop. `main2`(3))

`L(m) = L(m†)` where `m† = (mw_step m).2` is the MW residual. The RSK ladder is
determined by the fiber maxes of the depth function; Lemma `pre1` controls how depths
change from `m` to `m†`: they are preserved except on *special* segments (same-begin
proper subsegments of a chain element at the same depth), which move up by exactly one.

Layers:
1. greedy structure of `MW.extendChain.go` — prefix decomposition, maximality of the
   last chain element, minimal-end property of each greedy step;
2. structure of `makeResidual` membership;
3. transfer `depth_m ≤ depth_m†` (ladder push-forward with chain normalization);
4. the hard induction `depth_m† ≤ depth_m + 1`, `+1` only for special segments;
5. fiber-max preservation and `ladderRungs m† = ladderRungs m`.
-/

/-! ## Layer 1: greedy structure of `extendChain.go` -/

/-- The greedy scan only appends: its result is `chain ++ suffix` with the suffix
drawn from the scanned list. -/
lemma go_prefix (ms chain : List Segment) (hne : chain ≠ []) :
    ∃ suf, MW.extendChain.go ms chain hne = chain ++ suf ∧ ∀ y ∈ suf, y ∈ ms := by
  induction ms generalizing chain hne with
  | nil => exact ⟨[], by rw [MW.extendChain.go]; simp, by simp⟩
  | cons s rest ih =>
    rw [MW.extendChain.go]
    split_ifs with h
    · obtain ⟨suf, heq, hmem⟩ := ih (chain ++ [s]) (by simp)
      refine ⟨s :: suf, by rw [heq]; simp, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy'
      · simp
      · simp [hmem y hy']
    · obtain ⟨suf, heq, hmem⟩ := ih chain hne
      exact ⟨suf, heq, fun y hy => by simp [hmem y hy]⟩

/-- The greedy scan never returns the empty list. -/
lemma go_ne_nil (ms chain : List Segment) (hne : chain ≠ []) :
    MW.extendChain.go ms chain hne ≠ [] := by
  obtain ⟨suf, heq, -⟩ := go_prefix ms chain hne
  rw [heq]
  simp [hne]

/-- The last element of the greedy result is the initial chain's last, or comes from
the scanned list. -/
lemma go_getLast?_cases (ms chain : List Segment) (hne : chain ≠ []) :
    (MW.extendChain.go ms chain hne).getLast? = chain.getLast? ∨
    ∃ y ∈ ms, (MW.extendChain.go ms chain hne).getLast? = some y := by
  induction ms generalizing chain hne with
  | nil => left; rw [MW.extendChain.go]
  | cons s rest ih =>
    rw [MW.extendChain.go]
    split_ifs with h
    · rcases ih (chain ++ [s]) (by simp) with h1 | ⟨y, hy, h2⟩
      · right
        exact ⟨s, by simp, by rw [h1]; simp⟩
      · right
        exact ⟨y, by simp [hy], h2⟩
    · rcases ih chain hne with h1 | ⟨y, hy, h2⟩
      · left; exact h1
      · right; exact ⟨y, by simp [hy], h2⟩

/-- **Maximality of the greedy chain**: no element of the (sorted) scanned list chain-links
from the result's last element. -/
lemma go_last_no_link : ∀ (ms : List Segment), ms.Pairwise (· ≤ ·) →
    ∀ (chain : List Segment) (hne : chain ≠ []),
    ∀ x ∈ ms, ∀ g, (MW.extendChain.go ms chain hne).getLast? = some g →
      ¬ MW.chainLink g x := by
  intro ms
  induction ms with
  | nil => intro _ _ _ x hx; simp at hx
  | cons s rest ih =>
    intro hsorted chain hne x hx g hg hlink
    have hrest_sorted := (List.pairwise_cons.mp hsorted).2
    have hs_le := (List.pairwise_cons.mp hsorted).1
    rw [MW.extendChain.go] at hg
    split_ifs at hg with hcl
    · rcases List.mem_cons.mp hx with hxs | hx'
      · -- x = s; identify g
        have h7 := congrArg Segment.a hxs
        rcases go_getLast?_cases rest (chain ++ [s]) (by simp) with h1 | ⟨y, hy, h2⟩
        · rw [hg] at h1
          have hgs : g = s := by
            rw [List.getLast?_concat] at h1
            exact Option.some.inj h1
          have h8 := congrArg Segment.a hgs
          have h9 := hlink.2
          simp only [] at h7 h8
          omega
        · rw [h2] at hg
          obtain rfl := Option.some.inj hg
          have hle := seg_le_imp_a_le (hs_le y hy)
          have h9 := hlink.2
          simp only [] at h7
          omega
      · exact ih hrest_sorted (chain ++ [s]) (by simp) x hx' g hg hlink
    · rcases List.mem_cons.mp hx with hxs | hx'
      · have h7 := congrArg Segment.a hxs
        rcases go_getLast?_cases rest chain hne with h1 | ⟨y, hy, h2⟩
        · rw [hg] at h1
          have hgl : chain.getLast? = some (chain.getLast hne) :=
            List.getLast?_eq_some_getLast hne
          rw [hgl] at h1
          obtain rfl := Option.some.inj h1
          rw [hxs] at hlink
          exact hcl hlink
        · rw [h2] at hg
          obtain rfl := Option.some.inj hg
          have hle := seg_le_imp_a_le (hs_le y hy)
          have h9 := hlink.2
          simp only [] at h7
          omega
      · exact ih hrest_sorted chain hne x hx' g hg hlink

/-- Index lookup at the split point: the left element. -/
lemma getElem?_split_left {α : Type*} (u v : List α) (σ σ' : α) :
    (u ++ σ :: σ' :: v)[u.length]? = some σ := by
  rw [List.getElem?_append_right (le_refl u.length)]
  simp

/-- Index lookup at the split point: the right element. -/
lemma getElem?_split_right {α : Type*} (u v : List α) (σ σ' : α) :
    (u ++ σ :: σ' :: v)[u.length + 1]? = some σ' := by
  rw [List.getElem?_append_right (by omega : u.length ≤ u.length + 1)]
  simp

/-- **Greedy minimal-end property**: if `(σ, σ')` are consecutive in the greedy result at
a position where `σ'` was appended from the scanned (sorted) list, then any `x` in the
scanned list that chain-links from `σ` has end at least `σ'.b`. -/
lemma go_min_end : ∀ (ms : List Segment), ms.Pairwise (· ≤ ·) →
    ∀ (chain : List Segment) (hne : chain ≠ []) (u v : List Segment) (σ σ' : Segment),
      MW.extendChain.go ms chain hne = u ++ σ :: σ' :: v →
      chain.length ≤ u.length + 1 →
      ∀ x ∈ ms, MW.chainLink σ x → σ'.b ≤ x.b := by
  intro ms
  induction ms with
  | nil =>
    intro _ chain hne u v σ σ' heq hlen x hx
    simp at hx
  | cons s rest ih =>
    intro hsorted chain hne u v σ σ' heq hlen x hx hlink
    have hrest_sorted := (List.pairwise_cons.mp hsorted).2
    have hs_le := (List.pairwise_cons.mp hsorted).1
    have hchainpos : 0 < chain.length := List.length_pos_of_ne_nil hne
    rw [MW.extendChain.go] at heq
    split_ifs at heq with hcl
    · -- s appended: result = go rest (chain ++ [s])
      rcases Nat.lt_or_ge u.length chain.length with hpos | hpos
      · -- boundary pair: u.length + 1 = chain.length, σ = chain.getLast, σ' = s
        obtain ⟨suf, hsuf, -⟩ := go_prefix rest (chain ++ [s]) (by simp)
        have hlists : u ++ σ :: σ' :: v = (chain ++ [s]) ++ suf := heq.symm.trans hsuf
        have hs' : σ' = s := by
          have h0 : (u ++ σ :: σ' :: v)[u.length + 1]?
              = ((chain ++ [s]) ++ suf)[u.length + 1]? := by rw [hlists]
          rw [getElem?_split_right] at h0
          rw [show u.length + 1 = chain.length by omega] at h0
          rw [List.getElem?_append_left (by simp),
            List.getElem?_append_right (le_refl chain.length)] at h0
          simp at h0
          exact h0
        have hσeq : σ = chain.getLast hne := by
          have h0 : (u ++ σ :: σ' :: v)[u.length]?
              = ((chain ++ [s]) ++ suf)[u.length]? := by rw [hlists]
          rw [getElem?_split_left] at h0
          rw [List.getElem?_append_left (by simp; omega),
            List.getElem?_append_left (by omega)] at h0
          have hgl : chain.getLast? = some (chain.getLast hne) :=
            List.getLast?_eq_some_getLast hne
          rw [List.getLast?_eq_getElem?] at hgl
          rw [show u.length = chain.length - 1 by omega, hgl] at h0
          exact Option.some.inj h0
        rcases List.mem_cons.mp hx with hxs | hx'
        · rw [hs', hxs]
        · -- x ∈ rest with x.a = σ.a + 1 = s.a; sorted gives s ≤ x, so s.b ≤ x.b
          have hxa : x.a = s.a := by
            have h1 := hlink.2
            have h2 := hcl.2
            rw [hσeq] at h1
            omega
          have h4 := MW.seg_b_le_of_le_of_a_eq (hs_le x hx') hxa.symm
          rw [hs']
          exact h4
      · -- interior pair: covered by IH on (chain ++ [s]); x = s is vacuous
        rcases List.mem_cons.mp hx with hxs | hx'
        · -- σ sits at index ≥ chain.length in (chain++[s]) ++ suf: σ = s or σ ∈ suf
          obtain ⟨suf, hsuf, hsufmem⟩ := go_prefix rest (chain ++ [s]) (by simp)
          have hlists : u ++ σ :: σ' :: v = (chain ++ [s]) ++ suf := heq.symm.trans hsuf
          have h0 : (u ++ σ :: σ' :: v)[u.length]?
              = ((chain ++ [s]) ++ suf)[u.length]? := by rw [hlists]
          rw [getElem?_split_left, List.append_assoc,
            List.getElem?_append_right (by omega)] at h0
          have hσmem : σ ∈ s :: suf := List.mem_of_getElem? h0.symm
          have hσ_ge : s ≤ σ := by
            rcases List.mem_cons.mp hσmem with heq' | hσ'
            · exact le_of_eq heq'.symm
            · exact hs_le σ (hsufmem σ hσ')
          have h5 := seg_le_imp_a_le hσ_ge
          have h6 := hlink.2
          have h7 := congrArg Segment.a hxs
          simp only [] at h7
          omega
        · exact ih hrest_sorted (chain ++ [s]) (by simp) u v σ σ' heq (by simp; omega)
            x hx' hlink
    · -- s rejected: result = go rest chain
      rcases List.mem_cons.mp hx with hxs | hx'
      · -- x = s: σ = chain.getLast (contradicts rejection) or σ from suf (vacuous)
        obtain ⟨suf, hsuf, hsufmem⟩ := go_prefix rest chain hne
        have hlists : u ++ σ :: σ' :: v = chain ++ suf := heq.symm.trans hsuf
        have h0 : (u ++ σ :: σ' :: v)[u.length]? = (chain ++ suf)[u.length]? := by
          rw [hlists]
        rw [getElem?_split_left] at h0
        rcases Nat.lt_or_ge u.length chain.length with hpos | hpos
        · rw [List.getElem?_append_left hpos] at h0
          have hσlast : σ = chain.getLast hne := by
            have hgl : chain.getLast? = some (chain.getLast hne) :=
              List.getLast?_eq_some_getLast hne
            rw [List.getLast?_eq_getElem?] at hgl
            rw [show u.length = chain.length - 1 by omega, hgl] at h0
            exact Option.some.inj h0
          rw [hxs] at hlink
          rw [hσlast] at hlink
          exact absurd hlink hcl
        · rw [List.getElem?_append_right hpos] at h0
          have hσmem : σ ∈ suf := List.mem_of_getElem? h0.symm
          have hσ_ge : s ≤ σ := hs_le σ (hsufmem σ hσmem)
          have h5 := seg_le_imp_a_le hσ_ge
          have h6 := hlink.2
          have h7 := congrArg Segment.a hxs
          simp only [] at h7
          omega
      · exact ih hrest_sorted chain hne u v σ σ' heq hlen x hx' hlink

/-! ## Layer 2a: leading-chain structure -/

/-- No element of `m` chain-links from the leading chain's last element. -/
lemma leadingChain_last_no_link (m : Multisegment) (x : Segment) (hx : x ∈ m.segments)
    (g : Segment) (hg : (MW.leadingChain m).val.segments.getLast? = some g) :
    ¬ MW.chainLink g x := by
  intro hlink
  have hm : m.segments ≠ [] := List.ne_nil_of_mem hx
  obtain ⟨first, rest, hseg⟩ := List.exists_cons_of_ne_nil hm
  have hgo := leadingChain_eq_go m first rest hseg
  have hsorted : rest.Pairwise (· ≤ ·) := by
    have h := m.is_sorted; rw [hseg] at h; exact (List.pairwise_cons.mp h).2
  rw [hgo] at hg
  rw [hseg] at hx
  rcases List.mem_cons.mp hx with hxf | hxr
  · have hgC : g ∈ (MW.leadingChain m).val.segments := by
      rw [hgo]; exact List.mem_of_getLast? hg
    have hgm : g ∈ m.segments := MW.leadingChain_subset m g hgC
    have h1 : first.a ≤ g.a := head_begin_le m first (by rw [hseg]; rfl) g hgm
    have h2 := hlink.2
    have h3 := congrArg Segment.a hxf
    simp only [] at h3
    omega
  · exact go_last_no_link rest hsorted [first] (by simp) x hxr g hg hlink

/-- Greedy minimal-end at leading-chain pairs: the chosen successor has the smallest end
among all valid continuations. -/
lemma leadingChain_min_end (m : Multisegment) (u v : List Segment) (σ σ' : Segment)
    (hsplit : (MW.leadingChain m).val.segments = u ++ σ :: σ' :: v)
    (x : Segment) (hx : x ∈ m.segments) (hlink : MW.chainLink σ x) : σ'.b ≤ x.b := by
  have hm : m.segments ≠ [] := List.ne_nil_of_mem hx
  obtain ⟨first, rest, hseg⟩ := List.exists_cons_of_ne_nil hm
  have hgo := leadingChain_eq_go m first rest hseg
  have hsorted : rest.Pairwise (· ≤ ·) := by
    have h := m.is_sorted; rw [hseg] at h; exact (List.pairwise_cons.mp h).2
  have hsplit' : MW.extendChain.go rest [first] (by simp) = u ++ σ :: σ' :: v := by
    rw [← hgo]; exact hsplit
  rw [hseg] at hx
  rcases List.mem_cons.mp hx with hxf | hxr
  · have hσC : σ ∈ (MW.leadingChain m).val.segments := by rw [hsplit]; simp
    have hσm := MW.leadingChain_subset m σ hσC
    have h1 : first.a ≤ σ.a := head_begin_le m first (by rw [hseg]; rfl) σ hσm
    have h2 := hlink.2
    have h3 := congrArg Segment.a hxf
    simp only [] at h3
    omega
  · exact go_min_end rest hsorted [first] (by simp) u v σ σ' hsplit' (by simp) x hxr hlink

/-- A leading-chain element with a valid continuation in `m` has a successor in the
chain: it is not the last element. -/
lemma leadingChain_succ_split (m : Multisegment) (σ : Segment)
    (hσ : σ ∈ (MW.leadingChain m).val.segments)
    (z : Segment) (hz : z ∈ m.segments) (hlink : MW.chainLink σ z) :
    ∃ u σ' v, (MW.leadingChain m).val.segments = u ++ σ :: σ' :: v := by
  obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem hσ
  cases l₂ with
  | nil =>
    exfalso
    have hlast : (MW.leadingChain m).val.segments.getLast? = some σ := by
      rw [hsplit, List.getLast?_concat]
    exact leadingChain_last_no_link m z hz σ hlast hlink
  | cons σ' l₂' => exact ⟨l₁, σ', l₂', hsplit⟩

/-- Consecutive leading-chain elements are chain-linked. -/
lemma leadingChain_consecutive_link (m : Multisegment) (u v : List Segment) (σ σ' : Segment)
    (hsplit : (MW.leadingChain m).val.segments = u ++ σ :: σ' :: v) :
    MW.chainLink σ σ' := by
  have hchain : MW.isChain (MW.leadingChain m).val.segments := (MW.leadingChain m).property
  rw [MW.isChain, hsplit] at hchain
  exact (List.isChain_append_cons_cons.mp hchain).2.1

/-- Under `min m < min L(m)`, no leading-chain segment is a singleton. -/
lemma chain_seg_nondegenerate (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a)
    (σ : Segment) (hσ : σ ∈ (MW.leadingChain m).val.segments) : σ.a < σ.b := by
  have hσm := MW.leadingChain_subset m σ hσ
  obtain ⟨l₁, i, t, l₂, hsplit, hia, hta⟩ :=
    chain_seg_boundary m sₘ s_l hsₘ hs_l hmin σ hσ hσm
  by_contra hcon
  push_neg at hcon
  have hab : σ.a ≤ σ.b := σ.fst_le_snd
  have ht_bk : t ∈ (bucket m (depth_of_segment m σ hσm)).map (·.val) := by rw [hsplit]; simp
  obtain ⟨htm, htd⟩ := RSK.mem_bucket_depth m _ t ht_bk
  have hll : σ ≪ t := ⟨hta, by have h9 : t.a ≤ t.b := t.fst_le_snd; omega⟩
  have := ll_ne_depth m σ t hσm htm hll
  omega

/-! ## Layer 2b: structure of `makeResidual` membership -/

/-- Membership in the MW residual, before sorting. -/
lemma mem_makeResidual_iff (m : Multisegment) (Cl : List Segment) (x : Segment) :
    x ∈ (MW.makeResidual m Cl).segments ↔
      x ∈ Cl.foldl List.erase m.segments ∨ x ∈ Cl.filterMap MW.segmentResidual := by
  simp only [MW.makeResidual]
  rw [(List.perm_insertionSort (· ≤ ·) _).mem_iff, List.mem_append]

/-- Erasing only removes: members of the fold are members of the base list. -/
lemma mem_of_mem_foldl_erase : ∀ (Cl l : List Segment) (x : Segment),
    x ∈ Cl.foldl List.erase l → x ∈ l := by
  intro Cl
  induction Cl with
  | nil => intro l x hx; exact hx
  | cons c cs ih =>
    intro l x hx
    rw [List.foldl_cons] at hx
    exact List.mem_of_mem_erase (ih _ x hx)

/-- A member whose value is not erased survives the fold. -/
lemma mem_foldl_erase_of_not_mem : ∀ (Cl l : List Segment) (x : Segment),
    x ∈ l → x ∉ Cl → x ∈ Cl.foldl List.erase l := by
  intro Cl
  induction Cl with
  | nil => intro l x hx _; exact hx
  | cons c cs ih =>
    intro l x hx hnx
    rw [List.foldl_cons]
    refine ih _ x ?_ (fun h => hnx (by simp [h]))
    exact (List.mem_erase_of_ne (fun h => hnx (by simp [h]))).mpr hx

/-- `segmentResidual` on a non-singleton. -/
lemma segmentResidual_eq (σ : Segment) (h : σ.a < σ.b) :
    MW.segmentResidual σ = some ⟨⟨σ.a + 1, σ.b⟩, by omega⟩ := by
  simp [MW.segmentResidual, h]

/-- Sources of residual chain segments. -/
lemma mem_filterMap_residual {Cl : List Segment} {y : Segment}
    (hy : y ∈ Cl.filterMap MW.segmentResidual) :
    ∃ σ ∈ Cl, σ.a < σ.b ∧ y.a = σ.a + 1 ∧ y.b = σ.b := by
  obtain ⟨σ, hσ, heq⟩ := List.mem_filterMap.mp hy
  by_cases h : σ.a < σ.b
  · rw [segmentResidual_eq σ h] at heq
    obtain rfl := Option.some.inj heq
    exact ⟨σ, hσ, h, rfl, rfl⟩
  · simp [MW.segmentResidual, h] at heq

/-- Non-singleton chain segments emit their left-shortened residual. -/
lemma residual_mem_filterMap {Cl : List Segment} {σ : Segment} (hσ : σ ∈ Cl)
    (h : σ.a < σ.b) :
    (⟨⟨σ.a + 1, σ.b⟩, by omega⟩ : Segment) ∈ Cl.filterMap MW.segmentResidual :=
  List.mem_filterMap.mpr ⟨σ, hσ, segmentResidual_eq σ h⟩

/-- Source classification of MW-residual members. -/
lemma mem_mdag_cases (m : Multisegment) (Cl : List Segment) (x : Segment)
    (hx : x ∈ (MW.makeResidual m Cl).segments) :
    x ∈ m.segments ∨ ∃ σ ∈ Cl, σ.a < σ.b ∧ x.a = σ.a + 1 ∧ x.b = σ.b := by
  rw [mem_makeResidual_iff] at hx
  rcases hx with h | h
  · exact Or.inl (mem_of_mem_foldl_erase Cl _ x h)
  · exact Or.inr (mem_filterMap_residual h)

/-- An `m`-member whose value is off the chain survives into the MW residual. -/
lemma survivor_mem_mdag (m : Multisegment) (Cl : List Segment) (x : Segment)
    (hx : x ∈ m.segments) (hnx : x ∉ Cl) : x ∈ (MW.makeResidual m Cl).segments :=
  (mem_makeResidual_iff m Cl x).mpr (Or.inl (mem_foldl_erase_of_not_mem Cl _ x hx hnx))

/-- A non-singleton chain segment's residual is in the MW residual. -/
lemma starred_mem_mdag (m : Multisegment) (Cl : List Segment) (σ : Segment)
    (hσ : σ ∈ Cl) (h : σ.a < σ.b) :
    (⟨⟨σ.a + 1, σ.b⟩, by omega⟩ : Segment) ∈ (MW.makeResidual m Cl).segments :=
  (mem_makeResidual_iff m Cl _).mpr (Or.inr (residual_mem_filterMap hσ h))

/-! ## Layer 3: ladder transfer `depth_m ≤ depth_m†` -/

/-- Prepend to a `≪`-pairwise list given a link to its head. -/
lemma pairwise_ll_cons {l : List Segment} (hp : l.Pairwise (· ≪ ·))
    {h w : Segment} (hw : l.head? = some w) (hlink : h ≪ w) :
    (h :: l).Pairwise (· ≪ ·) := by
  have hcons := head?_eq_cons hw
  rw [List.pairwise_cons]
  refine ⟨?_, hp⟩
  intro y hy
  rw [hcons] at hy hp
  rcases List.mem_cons.mp hy with rfl | hyt
  · exact hlink
  · exact ll_trans _ _ _ hlink ((List.pairwise_cons.mp hp).1 y hyt)

/-- A `≪`-pairwise list of members of a multisegment is a sublist of it. -/
lemma ladder_sublist_of_mem (M : Multisegment) (l : List Segment)
    (hp : l.Pairwise (· ≪ ·)) (hmem : ∀ y ∈ l, y ∈ M.segments) : l <+ M.segments := by
  have hlt : l.Pairwise (· < ·) := hp.imp (fun {a b} h => Prod.Lex.left _ _ h.1)
  have hnd : l.Nodup := hlt.imp (fun {a b} h => ne_of_lt h)
  have hle : l.Pairwise (· ≤ ·) := hlt.imp (fun {a b} h => le_of_lt h)
  exact List.sublist_of_subperm_of_pairwise (List.subperm_of_subset hnd hmem) hle M.is_sorted

/-- Depth of a value from an explicit `≪`-pairwise witness list of members. -/
lemma depth_ge_of_ladder (M : Multisegment) (l : List Segment)
    (hp : l.Pairwise (· ≪ ·)) (hmem : ∀ y ∈ l, y ∈ M.segments)
    (x : Segment) (hx : l.head? = some x) (hxm : x ∈ M.segments) :
    l.length ≤ depth_of_segment M x hxm + 1 := by
  have hsub := ladder_sublist_of_mem M l hp hmem
  have hlad : isLadder l := by
    simp only [isLadder, decide_eq_true_eq]
    exact hp
  exact depth_witness' M x hxm ⟨⟨l, isLadder_sorted _ hlad⟩, hlad⟩ hsub
    (by rw [Option.mem_def]; exact hx)

/-- Extract a `≪`-pairwise member-witness list attaining the depth. -/
lemma ladder_of_depth (M : Multisegment) (x : Segment) (hxm : x ∈ M.segments) :
    ∃ l : List Segment, l.Pairwise (· ≪ ·) ∧ (∀ y ∈ l, y ∈ M.segments) ∧
      l.head? = some x ∧ l.length = depth_of_segment M x hxm + 1 := by
  obtain ⟨L, hsub, hhead, hlen⟩ := depth_witness M x hxm
  refine ⟨L.val.segments, ?_, ?_, ?_, hlen.symm⟩
  · simpa [isLadder] using L.prop
  · exact fun y hy => hsub.subset hy
  · rwa [← Option.mem_def]

/-- Predecessor split around a non-head member. -/
lemma exists_pred_split {α : Type*} :
    ∀ (l : List α) (x : α), x ∈ l → l.head? ≠ some x →
    ∃ u p v, l = u ++ p :: x :: v := by
  intro l
  induction l with
  | nil => intro x hx; simp at hx
  | cons h t ih =>
    intro x hx hhead
    classical
    have hxh : x ≠ h := by
      intro heq; exact hhead (by rw [heq]; rfl)
    have hxt : x ∈ t := by
      rcases List.mem_cons.mp hx with heq | hxt
      · exact absurd heq hxh
      · exact hxt
    cases t with
    | nil => simp at hxt
    | cons h2 t2 =>
      by_cases hxh2 : x = h2
      · exact ⟨[], h, t2, by rw [hxh2]; rfl⟩
      · obtain ⟨u, p, v, heq⟩ := ih x hxt (by simp [Ne.symm hxh2])
        exact ⟨h :: u, p, v, by rw [heq]; rfl⟩

/-- **Ladder transfer**: an `m`-ladder maps to an `m†`-ladder of the same length, with the
head sent to its starred value. Chain elements are replaced by their left-shortened
residuals; when a chain element is followed at begin-distance one by a non-chain element,
the successor is normalized to the chain's own successor (greedy minimal end). -/
lemma ladder_transfer (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a) :
    ∀ (n : ℕ) (l : List Segment), l.length = n → l.Pairwise (· ≪ ·) →
      (∀ y ∈ l, y ∈ m.segments) →
      ∀ x, l.head? = some x →
      ∃ l' : List Segment, l'.Pairwise (· ≪ ·) ∧ l'.length = l.length ∧
        (∀ y ∈ l', y ∈ (MW.makeResidual m (MW.leadingChain m).val.segments).segments) ∧
        ((x ∉ (MW.leadingChain m).val.segments → l'.head? = some x) ∧
         (∀ _ : x ∈ (MW.leadingChain m).val.segments,
           ∃ y', l'.head? = some y' ∧ y'.a = x.a + 1 ∧ y'.b = x.b)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro l hlen hp hmem x hx
    obtain ⟨rest, rfl⟩ : ∃ rest, l = x :: rest := ⟨l.tail, head?_eq_cons hx⟩
    · have hxm : x ∈ m.segments := hmem x (by simp)
      have hrest_p : rest.Pairwise (· ≪ ·) := (List.pairwise_cons.mp hp).2
      have hx_rel : ∀ y ∈ rest, x ≪ y := (List.pairwise_cons.mp hp).1
      cases rest with
      | nil =>
        -- singleton ladder
        by_cases hxC : x ∈ (MW.leadingChain m).val.segments
        · have hnd := chain_seg_nondegenerate m sₘ s_l hsₘ hs_l hmin x hxC
          refine ⟨[⟨⟨x.a + 1, x.b⟩, by omega⟩], by simp, by simp, ?_, ?_, ?_⟩
          · intro y hy
            simp only [List.mem_singleton] at hy
            subst hy
            exact starred_mem_mdag m _ x hxC hnd
          · intro hxC'; exact absurd hxC hxC'
          · intro _; exact ⟨_, rfl, rfl, rfl⟩
        · refine ⟨[x], by simp, by simp, ?_, fun _ => rfl, fun hxC' => absurd hxC' hxC⟩
          intro y hy
          simp only [List.mem_singleton] at hy
          subst hy
          exact survivor_mem_mdag m _ _ hxm hxC
      | cons z rest' =>
        have hz_m : z ∈ m.segments := hmem z (by simp)
        have hxz : x ≪ z := hx_rel z (by simp)
        by_cases hxC : x ∈ (MW.leadingChain m).val.segments
        · have hndx := chain_seg_nondegenerate m sₘ s_l hsₘ hs_l hmin x hxC
          by_cases hzC : z ∈ (MW.leadingChain m).val.segments
          · -- both on the chain: star both, recurse on the tail
            obtain ⟨l'', hp'', hlen'', hmem'', hhead''⟩ :=
              ihn (z :: rest').length (by simp [← hlen]) (z :: rest') rfl hrest_p
                (fun y hy => hmem y (by simp [hy])) z rfl
            obtain ⟨y', hy'head, hy'a, hy'b⟩ := hhead''.2 hzC
            refine ⟨⟨⟨x.a + 1, x.b⟩, by omega⟩ :: l'', ?_, by simpa using hlen'', ?_, ?_, ?_⟩
            · refine pairwise_ll_cons hp'' hy'head ⟨?_, ?_⟩
              · show x.a + 1 < y'.a
                have := hxz.1
                omega
              · show x.b < y'.b
                have := hxz.2
                omega
            · intro y hy
              rcases List.mem_cons.mp hy with rfl | hyc
              · exact starred_mem_mdag m _ x hxC hndx
              · exact hmem'' y hyc
            · intro hxC'; exact absurd hxC hxC'
            · intro _; exact ⟨_, rfl, rfl, rfl⟩
          · by_cases hza : z.a = x.a + 1
            · -- normalize: replace z by the chain successor of x
              have hlinkxz : MW.chainLink x z := ⟨hxz, hza⟩
              obtain ⟨u, σ', v, hsplit⟩ := leadingChain_succ_split m x hxC z hz_m hlinkxz
              have hlinkσ' := leadingChain_consecutive_link m u v x σ' hsplit
              have hσ'C : σ' ∈ (MW.leadingChain m).val.segments := by
                rw [hsplit]; simp
              have hσ'm : σ' ∈ m.segments := MW.leadingChain_subset m σ' hσ'C
              have hσ'end : σ'.b ≤ z.b := leadingChain_min_end m u v x σ' hsplit z hz_m hlinkxz
              -- replaced tail: σ' :: rest'
              have hp_new : (σ' :: rest').Pairwise (· ≪ ·) := by
                rw [List.pairwise_cons]
                refine ⟨?_, (List.pairwise_cons.mp hrest_p).2⟩
                intro w hw
                have hzw : z ≪ w := (List.pairwise_cons.mp hrest_p).1 w hw
                refine ⟨?_, ?_⟩
                · have h1 := hlinkσ'.2
                  have h2 := hzw.1
                  omega
                · have h2 := hzw.2
                  omega
              obtain ⟨l'', hp'', hlen'', hmem'', hhead''⟩ :=
                ihn (σ' :: rest').length (by simp [← hlen]) (σ' :: rest') rfl hp_new
                  (fun y hy => by
                    rcases List.mem_cons.mp hy with rfl | hyc
                    · exact hσ'm
                    · exact hmem y (by simp [hyc]))
                  σ' rfl
              obtain ⟨y', hy'head, hy'a, hy'b⟩ := hhead''.2 hσ'C
              refine ⟨⟨⟨x.a + 1, x.b⟩, by omega⟩ :: l'', ?_, ?_, ?_, ?_, ?_⟩
              · refine pairwise_ll_cons hp'' hy'head ⟨?_, ?_⟩
                · show x.a + 1 < y'.a
                  have := hlinkσ'.2
                  omega
                · show x.b < y'.b
                  have := hlinkσ'.1.2
                  omega
              · have h1 : (σ' :: rest').length = (z :: rest').length := by simp
                simp only [List.length_cons] at hlen'' ⊢
                omega
              · intro y hy
                rcases List.mem_cons.mp hy with rfl | hyc
                · exact starred_mem_mdag m _ x hxC hndx
                · exact hmem'' y hyc
              · intro hxC'; exact absurd hxC hxC'
              · intro _; exact ⟨_, rfl, rfl, rfl⟩
            · -- gap ≥ 2: star x links directly to star-of-z
              obtain ⟨l'', hp'', hlen'', hmem'', hhead''⟩ :=
                ihn (z :: rest').length (by simp [← hlen]) (z :: rest') rfl hrest_p
                  (fun y hy => hmem y (by simp [hy])) z rfl
              have hzhead := hhead''.1 hzC
              refine ⟨⟨⟨x.a + 1, x.b⟩, by omega⟩ :: l'', ?_, by simpa using hlen'', ?_, ?_, ?_⟩
              · refine pairwise_ll_cons hp'' hzhead ⟨?_, ?_⟩
                · show x.a + 1 < z.a
                  have := hxz.1
                  omega
                · show x.b < z.b
                  exact hxz.2
              · intro y hy
                rcases List.mem_cons.mp hy with rfl | hyc
                · exact starred_mem_mdag m _ x hxC hndx
                · exact hmem'' y hyc
              · intro hxC'; exact absurd hxC hxC'
              · intro _; exact ⟨_, rfl, rfl, rfl⟩
        · -- head off the chain: keep it, recurse
          obtain ⟨l'', hp'', hlen'', hmem'', hhead''⟩ :=
            ihn (z :: rest').length (by simp [← hlen]) (z :: rest') rfl hrest_p
              (fun y hy => hmem y (by simp [hy])) z rfl
          by_cases hzC : z ∈ (MW.leadingChain m).val.segments
          · obtain ⟨y', hy'head, hy'a, hy'b⟩ := hhead''.2 hzC
            refine ⟨x :: l'', ?_, by simpa using hlen'', ?_, fun _ => rfl, ?_⟩
            · refine pairwise_ll_cons hp'' hy'head ⟨?_, ?_⟩
              · show x.a < y'.a
                have := hxz.1
                omega
              · show x.b < y'.b
                have := hxz.2
                omega
            · intro y hy
              rcases List.mem_cons.mp hy with rfl | hyc
              · exact survivor_mem_mdag m _ _ hxm hxC
              · exact hmem'' y hyc
            · intro hxC'; exact absurd hxC' hxC
          · have hzhead := hhead''.1 hzC
            refine ⟨x :: l'', ?_, by simpa using hlen'', ?_, fun _ => rfl, ?_⟩
            · exact pairwise_ll_cons hp'' hzhead hxz
            · intro y hy
              rcases List.mem_cons.mp hy with rfl | hyc
              · exact survivor_mem_mdag m _ _ hxm hxC
              · exact hmem'' y hyc
            · intro hxC'; exact absurd hxC' hxC

/-- **Transfer ≥, off-chain values**: a surviving value is at least as deep in `m†`. -/
lemma depth_mdag_ge_notC (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a)
    (x : Segment) (hxm : x ∈ m.segments) (hxC : x ∉ (MW.leadingChain m).val.segments)
    (hx' : x ∈ (MW.makeResidual m (MW.leadingChain m).val.segments).segments) :
    depth_of_segment m x hxm ≤
      depth_of_segment (MW.makeResidual m (MW.leadingChain m).val.segments) x hx' := by
  obtain ⟨l, hp, hmem, hhead, hlen⟩ := ladder_of_depth m x hxm
  obtain ⟨l', hp', hlen', hmem', hhead'⟩ :=
    ladder_transfer m sₘ s_l hsₘ hs_l hmin l.length l rfl hp hmem x hhead
  have := depth_ge_of_ladder (MW.makeResidual m (MW.leadingChain m).val.segments)
    l' hp' hmem' x (hhead'.1 hxC) hx'
  omega

/-- **Transfer ≥, chain values**: the starred chain value is at least as deep in `m†`. -/
lemma depth_mdag_ge_inC (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a)
    (σ : Segment) (hσC : σ ∈ (MW.leadingChain m).val.segments)
    (y : Segment) (hya : y.a = σ.a + 1) (hyb : y.b = σ.b)
    (hy' : y ∈ (MW.makeResidual m (MW.leadingChain m).val.segments).segments) :
    ∀ (hσm : σ ∈ m.segments),
    depth_of_segment m σ hσm ≤
      depth_of_segment (MW.makeResidual m (MW.leadingChain m).val.segments) y hy' := by
  intro hσm
  obtain ⟨l, hp, hmem, hhead, hlen⟩ := ladder_of_depth m σ hσm
  obtain ⟨l', hp', hlen', hmem', hhead'⟩ :=
    ladder_transfer m sₘ s_l hsₘ hs_l hmin l.length l rfl hp hmem σ hhead
  obtain ⟨y', hy'head, hy'a, hy'b⟩ := hhead'.2 hσC
  have hyy' : y = y' := seg_ext (by omega) (by omega)
  subst hyy'
  have := depth_ge_of_ladder (MW.makeResidual m (MW.leadingChain m).val.segments)
    l' hp' hmem' y hy'head hy'
  omega

/-! ## Layer 4: the depth upper bound `depth_m† ≤ depth_m + 1`, `+1` only on specials -/

/-- **The σ₃-argument** (paper, proof of `pre1`, lines "Let i₃ = ⁻i₂ ∈ I*…"): given an
`m†`-element `w` over depth `D'' + 1` whose `m†`-predecessor `z` is a *special* survivor
at depth `D''` with `D'' = depth_m z + 1`, the chain predecessor `σ₃` of the special
witness produces a chain element with `depth_m σ₃ = D''` dominating `w`. -/
lemma sigma3_argument (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a)
    (D'' : ℕ)
    (hIH2 : ∀ d, d < D'' + 1 →
      ∀ (σ : Segment), σ ∈ (MW.leadingChain m).val.segments →
      ∀ (hσm : σ ∈ m.segments) (y : Segment), y.a = σ.a + 1 → y.b = σ.b →
      ∀ (hy' : y ∈ (MW.makeResidual m (MW.leadingChain m).val.segments).segments),
        depth_of_segment (MW.makeResidual m (MW.leadingChain m).val.segments) y hy' = d →
        d ≤ depth_of_segment m σ hσm)
    (w : Segment)
    (hw' : w ∈ (MW.makeResidual m (MW.leadingChain m).val.segments).segments)
    (hwD : depth_of_segment (MW.makeResidual m (MW.leadingChain m).val.segments) w hw'
      = D'' + 1)
    (z : Segment) (hzm : z ∈ m.segments)
    (hz' : z ∈ (MW.makeResidual m (MW.leadingChain m).val.segments).segments)
    (hzd : depth_of_segment (MW.makeResidual m (MW.leadingChain m).val.segments) z hz'
      = D'')
    (hwz : w ≪ z)
    (σ₂ : Segment) (hσ₂C : σ₂ ∈ (MW.leadingChain m).val.segments)
    (hσ₂m : σ₂ ∈ m.segments)
    (hza : z.a = σ₂.a) (hzb : z.b < σ₂.b)
    (hdep2 : depth_of_segment m z hzm = depth_of_segment m σ₂ hσ₂m)
    (hDz : D'' = depth_of_segment m z hzm + 1) :
    ∃ σ₃ ∈ (MW.leadingChain m).val.segments, ∃ hσ₃m : σ₃ ∈ m.segments,
      w.a ≤ σ₃.a ∧ w.b < σ₃.b ∧ depth_of_segment m σ₃ hσ₃m = D'' := by
  -- σ₂ is not the chain head
  have hσ₂ne : σ₂ ≠ sₘ := by
    intro heq
    have h1 : sₘ ≤ z := MW.head_le_mem m sₘ hsₘ z hzm
    have ha' := congrArg Segment.a heq
    have hb' := congrArg Segment.b heq
    simp only [] at ha' hb'
    have h2 : sₘ.b ≤ z.b := MW.seg_b_le_of_le_of_a_eq h1 (by omega)
    omega
  have hheadne : (MW.leadingChain m).val.segments.head? ≠ some σ₂ := by
    rw [MW.leadingChain_head m sₘ hsₘ]
    intro h
    exact hσ₂ne (Option.some.inj h).symm
  obtain ⟨u, σ₃, v, hsplit⟩ :=
    exists_pred_split (MW.leadingChain m).val.segments σ₂ hσ₂C hheadne
  have hlink₃₂ := leadingChain_consecutive_link m u v σ₃ σ₂ hsplit
  have hσ₃C : σ₃ ∈ (MW.leadingChain m).val.segments := by rw [hsplit]; simp
  have hσ₃m : σ₃ ∈ m.segments := MW.leadingChain_subset m σ₃ hσ₃C
  have hσ₃nd := chain_seg_nondegenerate m sₘ s_l hsₘ hs_l hmin σ₃ hσ₃C
  -- z's end is bounded by σ₃'s (greedy minimal end)
  have hzσ₃ : z.b ≤ σ₃.b := by
    by_contra hcon
    push_neg at hcon
    have hlinkz : MW.chainLink σ₃ z := by
      refine ⟨⟨?_, hcon⟩, ?_⟩
      · have := hlink₃₂.2; omega
      · have := hlink₃₂.2; omega
    have := leadingChain_min_end m u v σ₃ σ₂ hsplit z hzm hlinkz
    omega
  -- the starred σ₃ is an m†-element dominated-into by w
  have hstep : σ₃.a + 1 ≤ σ₃.b := by omega
  have hz₃' : (⟨⟨σ₃.a + 1, σ₃.b⟩, hstep⟩ : Segment)
      ∈ (MW.makeResidual m (MW.leadingChain m).val.segments).segments :=
    starred_mem_mdag m (MW.leadingChain m).val.segments σ₃ hσ₃C hσ₃nd
  have hwz₃ : w ≪ (⟨⟨σ₃.a + 1, σ₃.b⟩, hstep⟩ : Segment) := by
    refine ⟨?_, ?_⟩
    · show w.a < σ₃.a + 1
      have h1 := hwz.1
      have h2 := hlink₃₂.2
      omega
    · show w.b < σ₃.b
      have h1 := hwz.2
      omega
  have hz₃d := ll_ne_depth (MW.makeResidual m (MW.leadingChain m).val.segments)
    w _ hw' hz₃' hwz₃
  rw [hwD] at hz₃d
  -- IH(ii) at the depth of z₃, and the ≥-transfer, pin depth_m σ₃
  have hle := hIH2 _ (by omega) σ₃ hσ₃C hσ₃m
    (⟨⟨σ₃.a + 1, σ₃.b⟩, hstep⟩ : Segment) rfl rfl hz₃' rfl
  have hge := depth_mdag_ge_inC m sₘ s_l hsₘ hs_l hmin σ₃ hσ₃C
    (⟨⟨σ₃.a + 1, σ₃.b⟩, hstep⟩ : Segment) rfl rfl hz₃' hσ₃m
  -- depth_m σ₃ > depth_m σ₂ = D'' - 1
  have hgt : depth_of_segment m σ₂ hσ₂m < depth_of_segment m σ₃ hσ₃m :=
    ll_ne_depth m σ₃ σ₂ hσ₃m hσ₂m hlink₃₂.1
  refine ⟨σ₃, hσ₃C, hσ₃m, ?_, ?_, ?_⟩
  · have h1 := hwz.1
    have h2 := hlink₃₂.2
    omega
  · have h1 := hwz.2
    omega
  · omega

/-- **Lemma `pre1`(1)–(2), upper bounds**: an `m†`-depth exceeds the source's `m`-depth by
at most one, and exceeding it at all forces the source to be *special* — a same-begin
proper subsegment of a chain element at the same depth. Chain sources never exceed. -/
lemma mdag_depth_bound (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a) :
    ∀ (D' : ℕ),
      (∀ (x : Segment) (hxm : x ∈ m.segments)
        (hx' : x ∈ (MW.makeResidual m (MW.leadingChain m).val.segments).segments),
        depth_of_segment (MW.makeResidual m (MW.leadingChain m).val.segments) x hx' = D' →
        D' ≤ depth_of_segment m x hxm + 1 ∧
        (D' = depth_of_segment m x hxm + 1 →
          ∃ σ ∈ (MW.leadingChain m).val.segments, ∃ hσm : σ ∈ m.segments,
            x.a = σ.a ∧ x.b < σ.b ∧
            depth_of_segment m x hxm = depth_of_segment m σ hσm)) ∧
      (∀ (σ : Segment), σ ∈ (MW.leadingChain m).val.segments →
        ∀ (hσm : σ ∈ m.segments) (y : Segment), y.a = σ.a + 1 → y.b = σ.b →
        ∀ (hy' : y ∈ (MW.makeResidual m (MW.leadingChain m).val.segments).segments),
        depth_of_segment (MW.makeResidual m (MW.leadingChain m).val.segments) y hy' = D' →
        D' ≤ depth_of_segment m σ hσm) := by
  intro D'
  induction D' using Nat.strong_induction_on with
  | _ D' ih =>
    constructor
    · -- clause (i): surviving values
      intro x hxm hx' hd'
      rcases Nat.eq_zero_or_pos D' with hD0 | hDpos
      · exact ⟨by omega, fun heq => absurd heq (by omega)⟩
      · obtain ⟨D'', rfl⟩ : ∃ D'', D' = D'' + 1 := ⟨D' - 1, by omega⟩
        obtain ⟨z, hz', hzd, hxz⟩ := exists_pred_at_depth
          (MW.makeResidual m (MW.leadingChain m).val.segments) D'' x hx' hd'
        rcases mem_mdag_cases m (MW.leadingChain m).val.segments z hz'
          with hzm | ⟨τ, hτC, hτnd, hza, hzb⟩
        · -- predecessor is a survivor
          have hIHz := (ih D'' (by omega)).1 z hzm hz' hzd
          have hdep_z : depth_of_segment m z hzm < depth_of_segment m x hxm :=
            ll_ne_depth m x z hxm hzm hxz
          refine ⟨by omega, ?_⟩
          intro heq
          have h1 : D'' = depth_of_segment m z hzm + 1 := by omega
          obtain ⟨σ₂, hσ₂C, hσ₂m, hza2, hzb2, hzd2⟩ := hIHz.2 h1
          obtain ⟨σ₃, hσ₃C, hσ₃m, hwa3, hwb3, hd3⟩ :=
            sigma3_argument m sₘ s_l hsₘ hs_l hmin D''
              (fun d hd => (ih d (by omega)).2)
              x hx' hd' z hzm hz' hzd hxz σ₂ hσ₂C hσ₂m hza2 hzb2 hzd2 h1
          by_cases hxa3 : x.a = σ₃.a
          · exact ⟨σ₃, hσ₃C, hσ₃m, hxa3, hwb3, by omega⟩
          · exfalso
            have hx3 : x ≪ σ₃ := ⟨by omega, hwb3⟩
            have := ll_ne_depth m x σ₃ hxm hσ₃m hx3
            omega
        · -- predecessor is a starred chain value
          have hτm : τ ∈ m.segments := MW.leadingChain_subset m τ hτC
          have hIHτ := (ih D'' (by omega)).2 τ hτC hτm z hza hzb hz' hzd
          by_cases hxa : x.a = τ.a
          · have hxb : x.b < τ.b := by have := hxz.2; omega
            have helem : depth_of_segment m τ hτm ≤ depth_of_segment m x hxm :=
              depth_le_of_coord_le m x τ hxm hτm (by omega) (by omega)
            refine ⟨by omega, ?_⟩
            intro heq
            exact ⟨τ, hτC, hτm, hxa, hxb, by omega⟩
          · have hxτ : x ≪ τ := ⟨by have := hxz.1; omega, by have := hxz.2; omega⟩
            have hdep : depth_of_segment m τ hτm < depth_of_segment m x hxm :=
              ll_ne_depth m x τ hxm hτm hxτ
            exact ⟨by omega, fun heq => absurd heq (by omega)⟩
    · -- clause (ii): starred chain values
      intro σ hσC hσm y hya hyb hy' hd'
      rcases Nat.eq_zero_or_pos D' with hD0 | hDpos
      · omega
      · obtain ⟨D'', rfl⟩ : ∃ D'', D' = D'' + 1 := ⟨D' - 1, by omega⟩
        obtain ⟨z, hz', hzd, hyz⟩ := exists_pred_at_depth
          (MW.makeResidual m (MW.leadingChain m).val.segments) D'' y hy' hd'
        rcases mem_mdag_cases m (MW.leadingChain m).val.segments z hz'
          with hzm | ⟨τ, hτC, hτnd, hza, hzb⟩
        · -- predecessor is a survivor
          have hσz : σ ≪ z := ⟨by have := hyz.1; omega, by have := hyz.2; omega⟩
          have hdep_z : depth_of_segment m z hzm < depth_of_segment m σ hσm :=
            ll_ne_depth m σ z hσm hzm hσz
          have hIHz := (ih D'' (by omega)).1 z hzm hz' hzd
          by_contra hcon
          push_neg at hcon
          have h1 : D'' = depth_of_segment m z hzm + 1 := by omega
          obtain ⟨σ₂, hσ₂C, hσ₂m, hza2, hzb2, hzd2⟩ := hIHz.2 h1
          obtain ⟨σ₃, hσ₃C, hσ₃m, hwa3, hwb3, hd3⟩ :=
            sigma3_argument m sₘ s_l hsₘ hs_l hmin D''
              (fun d hd => (ih d (by omega)).2)
              y hy' hd' z hzm hz' hzd hyz σ₂ hσ₂C hσ₂m hza2 hzb2 hzd2 h1
          have hσ3 : σ ≪ σ₃ := ⟨by omega, by omega⟩
          have := ll_ne_depth m σ σ₃ hσm hσ₃m hσ3
          omega
        · -- predecessor is a starred chain value
          have hτm : τ ∈ m.segments := MW.leadingChain_subset m τ hτC
          have hστ : σ ≪ τ := ⟨by have := hyz.1; omega, by have := hyz.2; omega⟩
          have hdep : depth_of_segment m τ hτm < depth_of_segment m σ hσm :=
            ll_ne_depth m σ τ hσm hτm hστ
          have hIHτ := (ih D'' (by omega)).2 τ hτC hτm z hza hzb hz' hzd
          omega

/-! ## Layer 5: fiber maxes and the ladder equality -/

/-- `foldl max` over `ℕ` is the seed or attained. -/
lemma foldlMaxNat_mem_or (l : List ℕ) (i : ℕ) : l.foldl max i = i ∨ l.foldl max i ∈ l := by
  induction l generalizing i with
  | nil => exact Or.inl rfl
  | cons y ys ih =>
    rw [List.foldl_cons]
    rcases ih (max i y) with h | h
    · rw [h]
      rcases le_total i y with hle | hle
      · exact Or.inr (by rw [max_eq_right hle]; exact List.mem_cons_self)
      · exact Or.inl (max_eq_left hle)
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- A nonempty multisegment attains its `maxDepth`. -/
lemma maxDepth_attained (M : Multisegment) (hM : M.segments ≠ []) :
    ∃ x, ∃ hx : x ∈ M.segments, depth_of_segment M x hx = RSK.maxDepth M := by
  have h0 := foldlMaxNat_mem_or
    (M.segments.attach.map (fun p => depth_of_segment M p.val p.property)) 0
  rcases h0 with h | h
  · -- maxDepth = 0: any element has depth ≤ 0
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil M.segments hM
    refine ⟨x, hx, ?_⟩
    have h1 : depth_of_segment M x hx ≤ RSK.maxDepth M := RSK.depth_le_maxDepth M x hx
    have h2 : RSK.maxDepth M = 0 := h
    omega
  · obtain ⟨⟨x, hx⟩, -, heq⟩ := List.mem_map.mp h
    exact ⟨x, hx, heq⟩

/-- Every depth up to `maxDepth` carries a rung. -/
lemma rung_exists (M : Multisegment) (hM : M.segments ≠ []) (d : ℕ)
    (hd : d ≤ RSK.maxDepth M) : ∃ r, RSK.bucketRung M d = some r := by
  obtain ⟨x, hx, hxd⟩ := maxDepth_attained M hM
  rcases Nat.lt_or_ge d (RSK.maxDepth M) with hlt | hge
  · obtain ⟨x', hx', hx'd, -⟩ := exists_lower_ll (RSK.maxDepth M) M x hx hxd d hlt
    exact RSK.bucketRung_some_of_mem M d x' (RSK.mem_bucket_of_depth M d x' hx' hx'd)
  · have hdeq : d = RSK.maxDepth M := by omega
    rw [hdeq]
    exact RSK.bucketRung_some_of_mem M _ x (RSK.mem_bucket_of_depth M _ x hx hxd)

/-- Rung begins are antitone in depth (already with the exact gap). -/
lemma rung_a_mono (M : Multisegment) (d t : ℕ) (hdt : d ≤ t)
    (r_d r_t : Segment) (hr_d : RSK.bucketRung M d = some r_d)
    (hr_t : RSK.bucketRung M t = some r_t) : r_t.a ≤ r_d.a := by
  have := rung_a_gap M (t - d) d r_d r_t hr_d (by rw [Nat.add_sub_cancel' hdt]; exact hr_t)
  omega

/-- Rung ends are antitone in depth. -/
lemma rung_b_mono (M : Multisegment) (d t : ℕ) (hdt : d ≤ t)
    (r_d r_t : Segment) (hr_d : RSK.bucketRung M d = some r_d)
    (hr_t : RSK.bucketRung M t = some r_t) : r_t.b ≤ r_d.b := by
  rcases Nat.lt_or_ge d t with hlt | hge
  · obtain ⟨r', hr', hll⟩ := RSK.rung_lt_ll M t r_t hr_t d hlt
    rw [hr_d] at hr'
    obtain rfl := Option.some.inj hr'
    exact le_of_lt hll.2
  · have : d = t := by omega
    subst this
    rw [hr_d] at hr_t
    obtain rfl := Option.some.inj hr_t
    exact le_refl _

/-- **Special segments are dominated by the witness's chain predecessor**: a special `y`
(same begin, shorter end, same depth as chain element `σw`) has `y.a = σ₃.a + 1` and
`y.b ≤ σ₃.b` for the chain predecessor `σ₃` of `σw`, which is strictly deeper than `σw`. -/
lemma special_bounds (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (_ : (RSK.ladderRungs m).head? = some s_l) (_ : sₘ.a < s_l.a)
    (y : Segment) (hym : y ∈ m.segments)
    (σw : Segment) (hσwC : σw ∈ (MW.leadingChain m).val.segments)
    (hσwm : σw ∈ m.segments) (hya : y.a = σw.a) (hyb : y.b < σw.b) :
    ∃ σ₃ ∈ (MW.leadingChain m).val.segments, ∃ hσ₃m : σ₃ ∈ m.segments,
      y.a = σ₃.a + 1 ∧ y.b ≤ σ₃.b ∧
      depth_of_segment m σw hσwm < depth_of_segment m σ₃ hσ₃m := by
  -- σw is not the chain head
  have hσwne : σw ≠ sₘ := by
    intro heq
    have h1 : sₘ ≤ y := MW.head_le_mem m sₘ hsₘ y hym
    have ha' := congrArg Segment.a heq
    have hb' := congrArg Segment.b heq
    simp only [] at ha' hb'
    have h2 : sₘ.b ≤ y.b := MW.seg_b_le_of_le_of_a_eq h1 (by omega)
    omega
  have hheadne : (MW.leadingChain m).val.segments.head? ≠ some σw := by
    rw [MW.leadingChain_head m sₘ hsₘ]
    intro h
    exact hσwne (Option.some.inj h).symm
  obtain ⟨u, σ₃, v, hsplit⟩ :=
    exists_pred_split (MW.leadingChain m).val.segments σw hσwC hheadne
  have hlink₃w := leadingChain_consecutive_link m u v σ₃ σw hsplit
  have hσ₃C : σ₃ ∈ (MW.leadingChain m).val.segments := by rw [hsplit]; simp
  have hσ₃m : σ₃ ∈ m.segments := MW.leadingChain_subset m σ₃ hσ₃C
  have hyσ₃ : y.b ≤ σ₃.b := by
    by_contra hcon
    push_neg at hcon
    have hlinky : MW.chainLink σ₃ y := by
      refine ⟨⟨?_, hcon⟩, ?_⟩
      · have := hlink₃w.2; omega
      · have := hlink₃w.2; omega
    have := leadingChain_min_end m u v σ₃ σw hsplit y hym hlinky
    omega
  exact ⟨σ₃, hσ₃C, hσ₃m, by have := hlink₃w.2; omega, hyσ₃,
    ll_ne_depth m σ₃ σw hσ₃m hσwm hlink₃w.1⟩

/-- **Fiber upper bounds (α)**: every `m†`-element at `m†`-depth `d` is coordinatewise
below the `m`-rung of depth `d`. -/
lemma mdag_fiber_bounds (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a)
    (hmax : m.segments ≠ [])
    (d : ℕ) (r_d : Segment) (hr_d : RSK.bucketRung m d = some r_d)
    (y : Segment)
    (hy' : y ∈ (MW.makeResidual m (MW.leadingChain m).val.segments).segments)
    (hyd : depth_of_segment (MW.makeResidual m (MW.leadingChain m).val.segments) y hy' = d) :
    y.a ≤ r_d.a ∧ y.b ≤ r_d.b := by
  rcases mem_mdag_cases m (MW.leadingChain m).val.segments y hy'
    with hym | ⟨τ, hτC, hτnd, hya, hyb⟩
  · -- survivor
    have hbound := (mdag_depth_bound m sₘ s_l hsₘ hs_l hmin d).1 y hym hy' hyd
    rcases Nat.lt_or_ge (depth_of_segment m y hym) d with hlt | hge
    · -- one level up: special
      have heq : d = depth_of_segment m y hym + 1 := by omega
      obtain ⟨σw, hσwC, hσwm, hyaw, hybw, hdw⟩ := hbound.2 heq
      obtain ⟨σ₃, hσ₃C, hσ₃m, hya3, hyb3, hdgt⟩ :=
        special_bounds m sₘ s_l hsₘ hs_l hmin y hym σw hσwC hσwm hyaw hybw
      have ht₃d : d ≤ depth_of_segment m σ₃ hσ₃m := by omega
      have ht₃max := RSK.depth_le_maxDepth m σ₃ hσ₃m
      obtain ⟨r₃, hr₃⟩ := rung_exists m hmax _ ht₃max
      have hσ₃lt : σ₃.a < r₃.a :=
        chain_seg_lt_rung m sₘ s_l hsₘ hs_l hmin σ₃ hσ₃C hσ₃m r₃ hr₃
      obtain ⟨hdom, -, -⟩ := RSK.bucketRung_spec m _ r₃ hr₃
      have hσ₃in : σ₃ ∈ (bucket m (depth_of_segment m σ₃ hσ₃m)).map (·.val) :=
        RSK.mem_bucket_of_depth m _ σ₃ hσ₃m rfl
      obtain ⟨-, hσ₃b⟩ := hdom σ₃ hσ₃in
      have hma := rung_a_mono m d _ ht₃d r_d r₃ hr_d hr₃
      have hmb := rung_b_mono m d _ ht₃d r_d r₃ hr_d hr₃
      exact ⟨by omega, by omega⟩
    · -- at least as deep in m: monotone rung bounds
      have hdepmax := RSK.depth_le_maxDepth m y hym
      obtain ⟨r₁, hr₁⟩ := rung_exists m hmax _ hdepmax
      obtain ⟨hdom, -, -⟩ := RSK.bucketRung_spec m _ r₁ hr₁
      have hyin : y ∈ (bucket m (depth_of_segment m y hym)).map (·.val) :=
        RSK.mem_bucket_of_depth m _ y hym rfl
      obtain ⟨hyra, hyrb⟩ := hdom y hyin
      have hma := rung_a_mono m d _ hge r_d r₁ hr_d hr₁
      have hmb := rung_b_mono m d _ hge r_d r₁ hr_d hr₁
      exact ⟨by omega, by omega⟩
  · -- starred chain value
    have hτm := MW.leadingChain_subset m τ hτC
    have hd_le := (mdag_depth_bound m sₘ s_l hsₘ hs_l hmin d).2 τ hτC hτm y hya hyb hy' hyd
    have htmax := RSK.depth_le_maxDepth m τ hτm
    obtain ⟨r_t, hr_t⟩ := rung_exists m hmax _ htmax
    have hτlt : τ.a < r_t.a :=
      chain_seg_lt_rung m sₘ s_l hsₘ hs_l hmin τ hτC hτm r_t hr_t
    obtain ⟨hdom, -, -⟩ := RSK.bucketRung_spec m _ r_t hr_t
    have hτin : τ ∈ (bucket m (depth_of_segment m τ hτm)).map (·.val) :=
      RSK.mem_bucket_of_depth m _ τ hτm rfl
    obtain ⟨-, hτb⟩ := hdom τ hτin
    have hma := rung_a_mono m d _ hd_le r_d r_t hr_d hr_t
    have hmb := rung_b_mono m d _ hd_le r_d r_t hr_d hr_t
    exact ⟨by omega, by omega⟩

/-- **Fiber attainment (β)**: both rung coordinates of depth `d` are attained inside the
`m†`-fiber of depth `d`. -/
lemma mdag_fiber_attains (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a)
    (_ : m.segments ≠ [])
    (d : ℕ) (r_d : Segment) (hr_d : RSK.bucketRung m d = some r_d) :
    (∃ y, ∃ hy' : y ∈ (MW.makeResidual m (MW.leadingChain m).val.segments).segments,
      depth_of_segment (MW.makeResidual m (MW.leadingChain m).val.segments) y hy' = d ∧
      y.a = r_d.a) ∧
    (∃ y, ∃ hy' : y ∈ (MW.makeResidual m (MW.leadingChain m).val.segments).segments,
      depth_of_segment (MW.makeResidual m (MW.leadingChain m).val.segments) y hy' = d ∧
      y.b = r_d.b) := by
  obtain ⟨hdom, ⟨xA, hxAin, hxAa⟩, ⟨xB, hxBin, hxBb⟩⟩ := RSK.bucketRung_spec m d r_d hr_d
  obtain ⟨hxAm, hxAd⟩ := RSK.mem_bucket_depth m d xA hxAin
  obtain ⟨hxBm, hxBd⟩ := RSK.mem_bucket_depth m d xB hxBin
  constructor
  · -- the a-attainer survives with unchanged depth
    have hxAC : xA ∉ (MW.leadingChain m).val.segments := by
      intro hC
      have := chain_seg_lt_rung m sₘ s_l hsₘ hs_l hmin xA hC hxAm r_d
        (by rw [hxAd]; exact hr_d)
      omega
    have hxA' := survivor_mem_mdag m (MW.leadingChain m).val.segments xA hxAm hxAC
    have hge := depth_mdag_ge_notC m sₘ s_l hsₘ hs_l hmin xA hxAm hxAC hxA'
    have hbound := (mdag_depth_bound m sₘ s_l hsₘ hs_l hmin
      (depth_of_segment (MW.makeResidual m (MW.leadingChain m).val.segments) xA hxA')).1
      xA hxAm hxA' rfl
    have hns : depth_of_segment (MW.makeResidual m (MW.leadingChain m).val.segments) xA hxA'
        ≤ depth_of_segment m xA hxAm := by
      by_contra hcon
      push_neg at hcon
      have heq : depth_of_segment (MW.makeResidual m (MW.leadingChain m).val.segments) xA hxA'
          = depth_of_segment m xA hxAm + 1 := by omega
      obtain ⟨σw, hσwC, hσwm, hyaw, hybw, hdw⟩ := hbound.2 heq
      have := chain_seg_lt_rung m sₘ s_l hsₘ hs_l hmin σw hσwC hσwm r_d
        (by rw [← hdw, hxAd]; exact hr_d)
      omega
    exact ⟨xA, hxA', by omega, by omega⟩
  · by_cases hxBC : xB ∈ (MW.leadingChain m).val.segments
    · -- the b-attainer is the chain element: its residual attains b
      have hnd := chain_seg_nondegenerate m sₘ s_l hsₘ hs_l hmin xB hxBC
      have hstep : xB.a + 1 ≤ xB.b := by omega
      have hyB' : (⟨⟨xB.a + 1, xB.b⟩, hstep⟩ : Segment)
          ∈ (MW.makeResidual m (MW.leadingChain m).val.segments).segments :=
        starred_mem_mdag m (MW.leadingChain m).val.segments xB hxBC hnd
      have hge := depth_mdag_ge_inC m sₘ s_l hsₘ hs_l hmin xB hxBC
        (⟨⟨xB.a + 1, xB.b⟩, hstep⟩ : Segment) rfl rfl hyB' hxBm
      have hle := (mdag_depth_bound m sₘ s_l hsₘ hs_l hmin
        (depth_of_segment (MW.makeResidual m (MW.leadingChain m).val.segments) _ hyB')).2
        xB hxBC hxBm (⟨⟨xB.a + 1, xB.b⟩, hstep⟩ : Segment) rfl rfl hyB' rfl
      refine ⟨_, hyB', by omega, ?_⟩
      have hg : Segment.b (⟨⟨xB.a + 1, xB.b⟩, hstep⟩ : Segment) = xB.b := rfl
      omega
    · -- the b-attainer survives with unchanged depth
      have hxB' := survivor_mem_mdag m (MW.leadingChain m).val.segments xB hxBm hxBC
      have hge := depth_mdag_ge_notC m sₘ s_l hsₘ hs_l hmin xB hxBm hxBC hxB'
      have hbound := (mdag_depth_bound m sₘ s_l hsₘ hs_l hmin
        (depth_of_segment (MW.makeResidual m (MW.leadingChain m).val.segments) xB hxB')).1
        xB hxBm hxB' rfl
      have hns : depth_of_segment (MW.makeResidual m (MW.leadingChain m).val.segments) xB hxB'
          ≤ depth_of_segment m xB hxBm := by
        by_contra hcon
        push_neg at hcon
        have heq : depth_of_segment (MW.makeResidual m (MW.leadingChain m).val.segments)
            xB hxB' = depth_of_segment m xB hxBm + 1 := by omega
        obtain ⟨σw, hσwC, hσwm, hyaw, hybw, hdw⟩ := hbound.2 heq
        -- the witness sits in the same fiber, so its end is bounded by the rung's
        obtain ⟨hdomd, -, -⟩ := RSK.bucketRung_spec m d r_d hr_d
        have hσwin : σw ∈ (bucket m d).map (·.val) :=
          RSK.mem_bucket_of_depth m d σw hσwm (by omega)
        obtain ⟨-, hσwb⟩ := hdomd σw hσwin
        omega
      exact ⟨xB, hxB', by omega, by omega⟩

/-- **(γ) `maxDepth` is preserved.** -/
lemma mdag_maxDepth_eq (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a)
    (hmax : m.segments ≠ [])
    (hmax' : (MW.makeResidual m (MW.leadingChain m).val.segments).segments ≠ []) :
    RSK.maxDepth (MW.makeResidual m (MW.leadingChain m).val.segments) = RSK.maxDepth m := by
  apply le_antisymm
  · obtain ⟨y, hy', hyd⟩ := maxDepth_attained _ hmax'
    rcases mem_mdag_cases m (MW.leadingChain m).val.segments y hy'
      with hym | ⟨τ, hτC, hτnd, hya, hyb⟩
    · have hbound := (mdag_depth_bound m sₘ s_l hsₘ hs_l hmin _).1 y hym hy' hyd
      rcases Nat.lt_or_ge (depth_of_segment m y hym)
        (RSK.maxDepth (MW.makeResidual m (MW.leadingChain m).val.segments)) with hlt | hge
      · have heq : RSK.maxDepth (MW.makeResidual m (MW.leadingChain m).val.segments)
            = depth_of_segment m y hym + 1 := by omega
        obtain ⟨σw, hσwC, hσwm, hyaw, hybw, hdw⟩ := hbound.2 heq
        obtain ⟨σ₃, -, hσ₃m, -, -, hdgt⟩ :=
          special_bounds m sₘ s_l hsₘ hs_l hmin y hym σw hσwC hσwm hyaw hybw
        have := RSK.depth_le_maxDepth m σ₃ hσ₃m
        omega
      · have := RSK.depth_le_maxDepth m y hym
        omega
    · have hτm := MW.leadingChain_subset m τ hτC
      have hle := (mdag_depth_bound m sₘ s_l hsₘ hs_l hmin _).2 τ hτC hτm y hya hyb hy' hyd
      have := RSK.depth_le_maxDepth m τ hτm
      omega
  · obtain ⟨r, hr⟩ := rung_exists m hmax (RSK.maxDepth m) le_rfl
    obtain ⟨⟨y, hy', hyd, -⟩, -⟩ := mdag_fiber_attains m sₘ s_l hsₘ hs_l hmin hmax _ r hr
    have := RSK.depth_le_maxDepth (MW.makeResidual m (MW.leadingChain m).val.segments) y hy'
    omega

/-- **(δ) Every rung is preserved.** -/
lemma mdag_rung_eq (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a)
    (hmax : m.segments ≠ [])
    (d : ℕ) (hd : d ≤ RSK.maxDepth m) :
    RSK.bucketRung (MW.makeResidual m (MW.leadingChain m).val.segments) d
      = RSK.bucketRung m d := by
  obtain ⟨r_d, hr_d⟩ := rung_exists m hmax d hd
  obtain ⟨⟨yA, hyA', hyAd, hyAa⟩, ⟨yB, hyB', hyBd, hyBb⟩⟩ :=
    mdag_fiber_attains m sₘ s_l hsₘ hs_l hmin hmax d r_d hr_d
  have hyAin : yA ∈ ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments) d).map
      (·.val)) := RSK.mem_bucket_of_depth _ d yA hyA' hyAd
  have hyBin : yB ∈ ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments) d).map
      (·.val)) := RSK.mem_bucket_of_depth _ d yB hyB' hyBd
  obtain ⟨r', hr'⟩ := RSK.bucketRung_some_of_mem _ d yA hyAin
  obtain ⟨hdom', ⟨xa, hxain, hxaa⟩, ⟨xb, hxbin, hxbb⟩⟩ := RSK.bucketRung_spec _ d r' hr'
  rw [hr_d, hr']
  congr 1
  apply seg_ext
  · obtain ⟨hxam, hxad⟩ := RSK.mem_bucket_depth _ d xa hxain
    have hub := (mdag_fiber_bounds m sₘ s_l hsₘ hs_l hmin hmax d r_d hr_d xa hxam hxad).1
    obtain ⟨hyAra, -⟩ := hdom' yA hyAin
    omega
  · obtain ⟨hxbm, hxbd⟩ := RSK.mem_bucket_depth _ d xb hxbin
    have hub := (mdag_fiber_bounds m sₘ s_l hsₘ hs_l hmin hmax d r_d hr_d xb hxbm hxbd).2
    obtain ⟨-, hyBrb⟩ := hdom' yB hyBin
    omega

/-- **(ε) The ladder is preserved by `makeResidual` along the leading chain.** -/
lemma mdag_ladder_eq (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a)
    (hmax : m.segments ≠ []) :
    RSK.ladderRungs (MW.makeResidual m (MW.leadingChain m).val.segments)
      = RSK.ladderRungs m := by
  -- m† is nonempty: the starred chain head lives there
  obtain ⟨first, rest, hseg⟩ := List.exists_cons_of_ne_nil hmax
  have hCne : (MW.leadingChain m).val.segments ≠ [] := by
    rw [leadingChain_eq_go m first rest hseg]
    exact go_ne_nil rest [first] (by simp)
  obtain ⟨σ₀, hσ₀⟩ := List.exists_mem_of_ne_nil _ hCne
  have hσ₀nd := chain_seg_nondegenerate m sₘ s_l hsₘ hs_l hmin σ₀ hσ₀
  have hmax' : (MW.makeResidual m (MW.leadingChain m).val.segments).segments ≠ [] :=
    List.ne_nil_of_mem (starred_mem_mdag m (MW.leadingChain m).val.segments σ₀ hσ₀ hσ₀nd)
  unfold RSK.ladderRungs
  rw [mdag_maxDepth_eq m sₘ s_l hsₘ hs_l hmin hmax hmax']
  apply List.filterMap_congr
  intro d hd
  have hdle : d ≤ RSK.maxDepth m := by
    rw [List.mem_reverse, List.mem_range] at hd
    omega
  exact mdag_rung_eq m sₘ s_l hsₘ hs_l hmin hmax d hdle

/-- The MW residual of `mw_step` is `makeResidual` along the leading chain. -/
lemma mw_step_snd_eq (m : Multisegment) (hm : m.segments ≠ []) :
    (MW.mw_step m hm).2 = MW.makeResidual m (MW.leadingChain m).val.segments := by
  show MW.makeResidual m (MW.extendChain.go m.segments [m.segments.head hm] (by simp)) = _
  rw [go_full_eq m _ (List.head?_eq_some_head hm) (by simp)]
