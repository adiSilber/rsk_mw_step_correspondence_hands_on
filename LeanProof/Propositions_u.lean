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

/-! ## Completing Lemma `pre1`: the two converse clauses -/

/-- **`pre1`(2), converse**: every special survivor moves up by *exactly* one: it sits
strictly above the starred witness in `m†`, whose depth is at least the witness's. -/
lemma special_moves_up (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a)
    (y : Segment) (hym : y ∈ m.segments)
    (hy' : y ∈ (MW.makeResidual m (MW.leadingChain m).val.segments).segments)
    (σw : Segment) (hσwC : σw ∈ (MW.leadingChain m).val.segments)
    (hσwm : σw ∈ m.segments) (hya : y.a = σw.a) (hyb : y.b < σw.b)
    (hdep : depth_of_segment m y hym = depth_of_segment m σw hσwm) :
    depth_of_segment (MW.makeResidual m (MW.leadingChain m).val.segments) y hy'
      = depth_of_segment m y hym + 1 := by
  have hnd := chain_seg_nondegenerate m sₘ s_l hsₘ hs_l hmin σw hσwC
  have hstep : σw.a + 1 ≤ σw.b := by omega
  have hz' : (⟨⟨σw.a + 1, σw.b⟩, hstep⟩ : Segment)
      ∈ (MW.makeResidual m (MW.leadingChain m).val.segments).segments :=
    starred_mem_mdag m (MW.leadingChain m).val.segments σw hσwC hnd
  have hll : y ≪ (⟨⟨σw.a + 1, σw.b⟩, hstep⟩ : Segment) := by
    refine ⟨?_, ?_⟩
    · show y.a < σw.a + 1
      omega
    · show y.b < σw.b
      omega
  have h1 := ll_ne_depth (MW.makeResidual m (MW.leadingChain m).val.segments)
    y _ hy' hz' hll
  have h2 := depth_mdag_ge_inC m sₘ s_l hsₘ hs_l hmin σw hσwC
    (⟨⟨σw.a + 1, σw.b⟩, hstep⟩ : Segment) rfl rfl hz' hσwm
  have h3 := (mdag_depth_bound m sₘ s_l hsₘ hs_l hmin
    (depth_of_segment (MW.makeResidual m (MW.leadingChain m).val.segments) y hy')).1
    y hym hy' rfl
  omega

/-- **`pre1`(2), final clause**: if a special segment exists with witness `σ'`, then the
chain predecessor of `σ'` sits exactly one level above `σ'`. -/
lemma special_witness_gap (m : Multisegment) (sₘ s_l : Segment)
    (_ : m.segments.head? = some sₘ)
    (_ : (RSK.ladderRungs m).head? = some s_l) (_ : sₘ.a < s_l.a)
    (y : Segment) (hym : y ∈ m.segments)
    (σ' : Segment) (hσ'm : σ' ∈ m.segments)
    (hya : y.a = σ'.a) (hyb : y.b < σ'.b)
    (hdep : depth_of_segment m y hym = depth_of_segment m σ' hσ'm)
    (u v : List Segment) (σp : Segment)
    (hsplit : (MW.leadingChain m).val.segments = u ++ σp :: σ' :: v)
    (hσpm : σp ∈ m.segments) :
    depth_of_segment m σp hσpm = depth_of_segment m σ' hσ'm + 1 := by
  have hlink := leadingChain_consecutive_link m u v σp σ' hsplit
  have hgt : depth_of_segment m σ' hσ'm < depth_of_segment m σp hσpm :=
    ll_ne_depth m σp σ' hσpm hσ'm hlink.1
  by_contra hcon
  -- y's end is bounded by σp's (greedy minimal end)
  have hyσp : y.b ≤ σp.b := by
    by_contra hc
    push_neg at hc
    have hlk : MW.chainLink σp y := by
      refine ⟨⟨?_, hc⟩, ?_⟩
      · have := hlink.2; omega
      · have := hlink.2; omega
    have := leadingChain_min_end m u v σp σ' hsplit y hym hlk
    omega
  -- a segment at the intermediate depth
  obtain ⟨w, hwm, hwd, hσpw⟩ := exists_lower_ll (depth_of_segment m σp hσpm) m σp hσpm rfl
    (depth_of_segment m σ' hσ'm + 1) (by omega)
  by_cases hwa : w.a = σ'.a
  · -- w is a same-begin shorter alternative to σ' — contradicts greedy minimality
    have hwe : w.b < σ'.b := by
      by_contra h
      push_neg at h
      have := depth_le_of_coord_le m σ' w hσ'm hwm (by omega) h
      omega
    have hlk : MW.chainLink σp w := ⟨hσpw, by have := hlink.2; omega⟩
    have := leadingChain_min_end m u v σp σ' hsplit w hwm hlk
    omega
  · -- otherwise y ≪ w, contradicting the depths
    have hyw : y ≪ w := by
      refine ⟨?_, ?_⟩
      · have h1 := hσpw.1
        have h2 := hlink.2
        omega
      · have h2 := hσpw.2
        omega
    have := ll_ne_depth m y w hym hwm hyw
    omega

/-! ## Toward the value identification of `leadingChain (residual m)` -/

/-- Consecutive positions give a split. -/
lemma split_of_getElem?_consecutive {α : Type*} :
    ∀ (l : List α) (j : ℕ) (x y : α), l[j]? = some x → l[j + 1]? = some y →
    ∃ u v, l = u ++ x :: y :: v ∧ u.length = j := by
  intro l
  induction l with
  | nil => intro j x y hx; simp at hx
  | cons h t ih =>
    intro j x y hx hy
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      cases t with
      | nil => simp at hy
      | cons h2 t2 =>
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hy
        exact ⟨[], t2, by rw [hx, hy]; rfl, rfl⟩
    | succ i =>
      rw [List.getElem?_cons_succ] at hx hy
      obtain ⟨u, v, heq, hlen⟩ := ih i x y hx hy
      exact ⟨h :: u, v, by rw [heq]; rfl, by simp [hlen]⟩

/-- A split gives the element at the split position. -/
lemma getElem?_of_split {α : Type*} (u v : List α) (x : α) (l : List α)
    (h : l = u ++ x :: v) : l[u.length]? = some x := by
  subst h
  rw [List.getElem?_append_right (le_refl u.length)]
  simp

/-- In an `a`-sorted list, the begin-block boundary pair at a given begin is unique:
two adjacent pairs whose left elements share a begin strictly below both right begins
coincide. -/
lemma boundary_unique (L : List Segment) (hsorted : L.Pairwise (·.a ≤ ·.a))
    (x y x' y' : Segment) (u v u' v' : List Segment)
    (hsp : L = u ++ x :: y :: v) (hsp' : L = u' ++ x' :: y' :: v')
    (hxx' : x.a = x'.a) (hxy : x.a < y.a) (hxy' : x'.a < y'.a) :
    x = x' ∧ y = y' := by
  -- both boundaries occur at the last index with begin `x.a`; hence the same position
  rcases Nat.lt_trichotomy u.length u'.length with hlt | heq | hgt
  · -- x' sits at index u'.length > u.length, i.e. within y :: v; so x'.a ≥ y.a > x.a = x'.a
    exfalso
    have h1 : L[u.length + 1]? = some y := by
      rw [hsp]; exact getElem?_split_right u v x y
    have h2 : L[u'.length]? = some x' := by
      rw [hsp']
      exact getElem?_of_split u' (y' :: v') x' _ rfl
    -- y ≤ x' in the pairwise order since u.length + 1 ≤ u'.length
    rcases Nat.eq_or_lt_of_le (by omega : u.length + 1 ≤ u'.length) with heq1 | hlt1
    · rw [heq1] at h1
      rw [h1] at h2
      obtain rfl := Option.some.inj h2
      omega
    · -- strictly later: use sortedness via the split around y
      have hsorted' := hsorted
      rw [hsp] at hsorted'
      have h3 : x' ∈ y :: v := by
        -- index u'.length lands in the (y :: v) part
        rw [hsp, List.getElem?_append_right (by omega : u.length ≤ u'.length)] at h2
        have h4 : u'.length - u.length = (u'.length - u.length - 1) + 1 := by omega
        rw [h4, List.getElem?_cons_succ] at h2
        have h5 : u'.length - u.length - 1 = (u'.length - u.length - 2) + 1 := by omega
        rw [h5, List.getElem?_cons_succ] at h2
        exact List.mem_cons_of_mem _ (List.mem_of_getElem? h2)
      have h5 := (List.pairwise_append.mp hsorted').2.1
      rcases List.mem_cons.mp h3 with rfl | h6
      · omega
      · have := (List.pairwise_cons.mp (List.pairwise_cons.mp h5).2).1 x' h6
        omega
  · -- same position: elements coincide
    have h1 : L[u.length]? = some x := by
      rw [hsp]; exact getElem?_of_split u (y :: v) x _ rfl
    have h2 : L[u'.length]? = some x' := by
      rw [hsp']; exact getElem?_of_split u' (y' :: v') x' _ rfl
    have h3 : L[u.length + 1]? = some y := by
      rw [hsp]; exact getElem?_split_right u v x y
    have h4 : L[u'.length + 1]? = some y' := by
      rw [hsp']; exact getElem?_split_right u' v' x' y'
    rw [heq] at h1 h3
    rw [h1] at h2
    rw [h3] at h4
    exact ⟨Option.some.inj h2, Option.some.inj h4⟩
  · -- symmetric to the first case
    exfalso
    have h1 : L[u'.length + 1]? = some y' := by
      rw [hsp']; exact getElem?_split_right u' v' x' y'
    have h2 : L[u.length]? = some x := by
      rw [hsp]; exact getElem?_of_split u (y :: v) x _ rfl
    rcases Nat.eq_or_lt_of_le (by omega : u'.length + 1 ≤ u.length) with heq1 | hlt1
    · rw [heq1] at h1
      rw [h1] at h2
      obtain rfl := Option.some.inj h2
      omega
    · have hsorted' := hsorted
      rw [hsp'] at hsorted'
      have h3 : x ∈ y' :: v' := by
        rw [hsp', List.getElem?_append_right (by omega : u'.length ≤ u.length)] at h2
        have h4 : u.length - u'.length = (u.length - u'.length - 1) + 1 := by omega
        rw [h4, List.getElem?_cons_succ] at h2
        have h5 : u.length - u'.length - 1 = (u.length - u'.length - 2) + 1 := by omega
        rw [h5, List.getElem?_cons_succ] at h2
        exact List.mem_cons_of_mem _ (List.mem_of_getElem? h2)
      have h5 := (List.pairwise_append.mp hsorted').2.1
      rcases List.mem_cons.mp h3 with rfl | h6
      · omega
      · have := (List.pairwise_cons.mp (List.pairwise_cons.mp h5).2).1 x h6
        omega

/-- Fiber elements are `⊆`-comparable (value form). -/
lemma bucket_val_comparable (M : Multisegment) (d : ℕ) (x y : Segment)
    (hx : x ∈ (bucket M d).map (·.val)) (hy : y ∈ (bucket M d).map (·.val)) :
    x ⊆ y ∨ y ⊆ x := by
  obtain ⟨⟨x', hx'⟩, hxbk, rfl⟩ := List.mem_map.mp hx
  obtain ⟨⟨y', hy'⟩, hybk, rfl⟩ := List.mem_map.mp hy
  exact bucket_sink M d _ _ hxbk hybk

/-- **Minimality at the chain head** (paper Prop. `main2`(2), case (a)): every residual
segment beginning at `min m` ends at or after the head's boundary partner. -/
lemma residual_min_end_base (m : Multisegment) (sₘ : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (σ0 : Segment) (hσ0 : (MW.leadingChain m).val.segments.head? = some σ0)
    (hσ0m : σ0 ∈ m.segments) (i t : Segment) (l₁ l₂ : List Segment)
    (hsplit : (bucket m (depth_of_segment m σ0 hσ0m)).map (·.val) = l₁ ++ i :: t :: l₂)
    (hia : i.a = σ0.a) (hta : σ0.a < t.a)
    (z : Segment) (hz : z ∈ (RSK.residual m).segments) (hza : z.a = σ0.a) :
    t.b ≤ z.b := by
  classical
  -- σ0 is the head value of m
  have hσ0sₘ : σ0 = sₘ := by
    have h1 := MW.leadingChain_head m sₘ hsₘ
    rw [hσ0] at h1
    exact Option.some.inj h1
  by_contra hcon
  push_neg at hcon
  obtain ⟨d_z, i_z, t_z, u_z, v_z, hdz_le, hsplit_z, hzia, hzib⟩ := residual_source m z hz
  have hiz_bk : i_z ∈ (bucket m d_z).map (·.val) := by rw [hsplit_z]; simp
  obtain ⟨hiz_m, hiz_d⟩ := RSK.mem_bucket_depth m d_z i_z hiz_bk
  have htz_bk : t_z ∈ (bucket m d_z).map (·.val) := by rw [hsplit_z]; simp
  obtain ⟨htz_m, htz_d⟩ := RSK.mem_bucket_depth m d_z t_z htz_bk
  have htztz := RSK.bucket_split_pair_subset m d_z i_z t_z u_z v_z hsplit_z
  obtain ⟨htz_a, htz_b⟩ := htztz
  -- σ0 ≤ i_z (head of m) with equal begins
  have hσ0iz : σ0.b ≤ i_z.b := by
    have h1 : sₘ ≤ i_z := MW.head_le_mem m sₘ hsₘ i_z hiz_m
    have h2 := MW.seg_b_le_of_le_of_a_eq h1 (by rw [hσ0sₘ] at hza; omega)
    rw [hσ0sₘ]
    exact h2
  -- t ⊆ σ0 within the head fiber
  have ht_bk : t ∈ (bucket m (depth_of_segment m σ0 hσ0m)).map (·.val) := by
    rw [hsplit]; simp
  have hσ0_bk : σ0 ∈ (bucket m (depth_of_segment m σ0 hσ0m)).map (·.val) :=
    RSK.mem_bucket_of_depth m _ σ0 hσ0m rfl
  have htσ0 : t.b ≤ σ0.b := by
    rcases bucket_val_comparable m _ t σ0 ht_bk hσ0_bk with h | h
    · exact h.2
    · obtain ⟨h1, -⟩ := h
      omega
  by_cases hicase : i_z = σ0
  · -- the source pair starts at the head value: its partner is either a same-begin
    -- shorter element (impossible for the minimum) or the boundary partner itself
    have hica := congrArg Segment.a hicase
    have hicb := congrArg Segment.b hicase
    simp only [] at hica hicb
    have hdz : d_z = depth_of_segment m σ0 hσ0m := by
      rw [← hiz_d]
      subst hicase
      rfl
    by_cases htza : t_z.a = σ0.a
    · -- t_z is a same-begin element ending strictly below the minimum's end
      have h1 : sₘ ≤ t_z := MW.head_le_mem m sₘ hsₘ t_z htz_m
      have h2 := MW.seg_b_le_of_le_of_a_eq h1 (by rw [← hσ0sₘ]; omega)
      have h3 := congrArg Segment.b hσ0sₘ
      simp only [] at h3
      omega
    · -- boundary pair: coincides with (i, t) by uniqueness
      have htza' : i_z.a < t_z.a := by omega
      rw [hdz] at hsplit_z
      obtain ⟨-, hteq⟩ := boundary_unique _ (bucket_sorted m _) i_z t_z i t
        u_z v_z l₁ l₂ hsplit_z hsplit (by omega) htza' (by omega)
      have := congrArg Segment.b hteq
      simp only [] at this
      omega
  · -- generic source: σ0 sits strictly between the pair, contradicting Lemma 2.2(1)
    have htzσ0 : t_z ⊆ σ0 := by
      refine ⟨?_, ?_⟩
      · omega
      · omega
    have hσ0iz' : σ0 ⊆ i_z := by
      refine ⟨?_, ?_⟩
      · omega
      · omega
    have hne_t : σ0 ≠ t_z := by
      intro heq
      have := congrArg Segment.b heq
      simp only [] at this
      omega
    have hlt := RSK.depth_lt_between_split m d_z i_z t_z u_z v_z hsplit_z σ0 hσ0m
      htzσ0 hσ0iz' (Ne.symm hicase) (fun h => hne_t h)
    -- yet σ0 is coordinatewise below i_z, so its depth dominates the pair's fiber
    have hdom := depth_le_of_coord_le m σ0 i_z hσ0m hiz_m (by omega) (by omega)
    omega

/-- **Minimality along the chain** (paper Prop. `main2`(2), case (b) second part): a
residual segment starting one past `σⱼ` and linkable from the derived segment `Wⱼ`
(its end exceeds `tⱼ.b`) ends at or after `σⱼ₊₁`'s boundary partner `t'`. The proof
replaces the source's outer segment `i_z` by a chain-linkable segment `m̃` at the same
depth, invokes greedy minimality of `σⱼ₊₁`, and squeezes the source fiber between the
two chain fibers. -/
lemma residual_min_end_step (m : Multisegment)
    (u v : List Segment) (σj σj1 : Segment)
    (hsplitC : (MW.leadingChain m).val.segments = u ++ σj :: σj1 :: v)
    (hσjm : σj ∈ m.segments) (hσj1m : σj1 ∈ m.segments)
    (i_j t_j : Segment) (l₁ l₂ : List Segment)
    (hsplit_j : (bucket m (depth_of_segment m σj hσjm)).map (·.val) = l₁ ++ i_j :: t_j :: l₂)
    (hia_j : i_j.a = σj.a) (_ : σj.a < t_j.a)
    (i' t' : Segment) (l₁' l₂' : List Segment)
    (hsplit' : (bucket m (depth_of_segment m σj1 hσj1m)).map (·.val) = l₁' ++ i' :: t' :: l₂')
    (_ : i'.a = σj1.a) (hta' : σj1.a < t'.a)
    (z : Segment) (hz : z ∈ (RSK.residual m).segments)
    (hza : z.a = σj1.a) (hzb : t_j.b < z.b) :
    t'.b ≤ z.b := by
  classical
  obtain ⟨hll, hsucc⟩ := leadingChain_consecutive_link m u v σj σj1 hsplitC
  by_contra hcon
  push_neg at hcon
  obtain ⟨d_z, i_z, t_z, u_z, v_z, hdz_le, hsplit_z, hzia, hzib⟩ := residual_source m z hz
  have hiz_bk : i_z ∈ (bucket m d_z).map (·.val) := by rw [hsplit_z]; simp
  obtain ⟨hiz_m, hiz_d⟩ := RSK.mem_bucket_depth m d_z i_z hiz_bk
  have htz_bk : t_z ∈ (bucket m d_z).map (·.val) := by rw [hsplit_z]; simp
  obtain ⟨htz_m, htz_d⟩ := RSK.mem_bucket_depth m d_z t_z htz_bk
  obtain ⟨htzi_a, htzi_b⟩ := RSK.bucket_split_pair_subset m d_z i_z t_z u_z v_z hsplit_z
  -- the source fiber sits strictly below σⱼ's fiber
  have hstep1 : d_z < depth_of_segment m σj hσjm := by
    have h := RSK.lemma_2_2_2_split m _ i_j t_j l₁ l₂ hsplit_j i_z hiz_m
      (by omega) (by omega)
    omega
  -- replace i_z by a chain-linkable segment m̃ at the same depth
  obtain ⟨mt, hmt_m, hmt_d, hmt_link⟩ :
      ∃ (mt : Segment) (hmt_m : mt ∈ m.segments),
        depth_of_segment m mt hmt_m = d_z ∧ MW.chainLink σj mt := by
    by_cases hcase : σj ≪ i_z
    · exact ⟨i_z, hiz_m, hiz_d, hcase, by omega⟩
    · have hib : i_z.b ≤ σj.b := by
        simp only [(· ≪ ·), ll, not_and, not_lt] at hcase
        exact hcase (by omega)
      obtain ⟨mt, hmt_m, hmt_d, hmt_ll⟩ :=
        exists_lower_ll _ m σj hσjm rfl d_z hstep1
      have hmt_a : mt.a = σj.a + 1 := by
        by_contra hne
        have h1 : i_z ≪ mt := by
          obtain ⟨h2, h3⟩ := hmt_ll
          exact ⟨by omega, by omega⟩
        have h2 := ll_ne_depth m i_z mt hiz_m hmt_m h1
        omega
      exact ⟨mt, hmt_m, hmt_d, hmt_ll, hmt_a⟩
  -- greedy minimality of σⱼ₊₁ against m̃, then squeeze the fibers
  have hgreedy : σj1.b ≤ mt.b :=
    leadingChain_min_end m u v σj σj1 hsplitC mt hmt_m hmt_link
  have hcoord := depth_le_of_coord_le m σj1 mt hσj1m hmt_m
    (by obtain ⟨-, h⟩ := hmt_link; omega) hgreedy
  have ht'_bk : t' ∈ (bucket m (depth_of_segment m σj1 hσj1m)).map (·.val) := by
    rw [hsplit']; simp
  obtain ⟨ht'_m, ht'_d⟩ := RSK.mem_bucket_depth m _ t' ht'_bk
  have hfinal := RSK.lemma_2_2_2_split m d_z i_z t_z u_z v_z hsplit_z t' ht'_m
    (by omega) (by omega)
  omega

/-- **C′ value identification** (paper Prop. `main2`(2), full form): the `j`-th segment
of the leading chain of the RSK residual `m′` is exactly the derived segment
`Wⱼ = ⟨σⱼ.a, tⱼ.b⟩` of the `j`-th chain segment's fiber boundary `(iⱼ, tⱼ)`. Proven by
induction on `j`: the base case is head-minimality (`residual_min_end_base`), the step
combines greedy minimality against `Wⱼ₊₁` with `residual_min_end_step`. -/
lemma leadingChain_residual_entries (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a) :
    ∀ (j : ℕ) (σ : Segment), (MW.leadingChain m).val.segments[j]? = some σ →
    ∃ (hσm : σ ∈ m.segments) (i t : Segment) (l₁ l₂ : List Segment),
      (bucket m (depth_of_segment m σ hσm)).map (·.val) = l₁ ++ i :: t :: l₂ ∧
      i.a = σ.a ∧ σ.a < t.a ∧
      ∃ w, (MW.leadingChain (RSK.residual m)).val.segments[j]? = some w ∧
        w.a = σ.a ∧ w.b = t.b := by
  intro j
  induction j with
  | zero =>
    intro σ hσ
    -- σ is the head value sₘ
    have hσhead : (MW.leadingChain m).val.segments.head? = some σ := by
      rw [List.head?_eq_getElem?]; exact hσ
    have hσsₘ : σ = sₘ := by
      have h1 := MW.leadingChain_head m sₘ hsₘ
      rw [hσhead] at h1
      exact Option.some.inj h1
    have hσa : σ.a = sₘ.a := by rw [hσsₘ]
    have hσC : σ ∈ (MW.leadingChain m).val.segments := List.mem_of_getElem? hσ
    have hσm := MW.leadingChain_subset m σ hσC
    obtain ⟨l₁, i, t, l₂, hsplit, hia, hta⟩ :=
      chain_seg_boundary m sₘ s_l hsₘ hs_l hmin σ hσC hσm
    refine ⟨hσm, i, t, l₁, l₂, hsplit, hia, hta, ?_⟩
    -- the derived segment of the head boundary lies in the residual
    obtain ⟨w0, hw0_bkres, hw0a, hw0b⟩ :=
      derived_mem_bucketResidual m _ i t l₁ l₂ hsplit
    have hw0_mem : w0 ∈ (RSK.residual m).segments :=
      mem_residual_of_bucket m (RSK.depth_le_maxDepth m σ hσm) hw0_bkres
    have hne' : (RSK.residual m).segments ≠ [] := List.ne_nil_of_mem hw0_mem
    obtain ⟨s_m', tl, hcons⟩ := List.exists_cons_of_ne_nil hne'
    have hs_m' : (RSK.residual m).segments.head? = some s_m' := by rw [hcons]; rfl
    have hs_m'_mem : s_m' ∈ (RSK.residual m).segments := by
      rw [hcons]; exact List.mem_cons_self
    have hheadC' := MW.leadingChain_head (RSK.residual m) s_m' hs_m'
    refine ⟨s_m', by rw [← List.head?_eq_getElem?]; exact hheadC', ?_, ?_⟩
    · have := minPreserved m sₘ hsₘ s_l hs_l hmin s_m' hs_m'
      omega
    · -- ≤: the head is lex-minimal and shares its begin with the derived segment
      have hle : s_m'.b ≤ t.b := by
        have h1 : s_m' ≤ w0 := MW.head_le_mem (RSK.residual m) s_m' hs_m' w0 hw0_mem
        have h2 : s_m'.a = sₘ.a := minPreserved m sₘ hsₘ s_l hs_l hmin s_m' hs_m'
        have h3 := MW.seg_b_le_of_le_of_a_eq h1 (by omega)
        omega
      -- ≥: head-fiber minimality
      have hge : t.b ≤ s_m'.b :=
        residual_min_end_base m sₘ hsₘ σ hσhead hσm i t l₁ l₂ hsplit hia hta
          s_m' hs_m'_mem
          (by have := minPreserved m sₘ hsₘ s_l hs_l hmin s_m' hs_m'; omega)
      omega
  | succ j ih =>
    intro σ1 hσ1
    -- the previous chain entry and its data from the induction hypothesis
    obtain ⟨hjlt, -⟩ := List.getElem?_eq_some_iff.mp hσ1
    have hσj : (MW.leadingChain m).val.segments[j]? =
        some ((MW.leadingChain m).val.segments[j]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    obtain ⟨hσjm, i_j, t_j, l₁j, l₂j, hsplit_j, hia_j, hta_j, wj, hwj, hwja, hwjb⟩ :=
      ih _ hσj
    set σj := (MW.leadingChain m).val.segments[j]'(by omega) with hσjdef
    -- consecutive chain split and link
    obtain ⟨u, v, hsplitC, -⟩ :=
      split_of_getElem?_consecutive _ j σj σ1 hσj hσ1
    obtain ⟨hll, hsucc⟩ := leadingChain_consecutive_link m u v σj σ1 hsplitC
    have hσ1C : σ1 ∈ (MW.leadingChain m).val.segments := List.mem_of_getElem? hσ1
    have hσ1m := MW.leadingChain_subset m σ1 hσ1C
    obtain ⟨l₁', i', t', l₂', hsplit', hia', hta'⟩ :=
      chain_seg_boundary m sₘ s_l hsₘ hs_l hmin σ1 hσ1C hσ1m
    refine ⟨hσ1m, i', t', l₁', l₂', hsplit', hia', hta', ?_⟩
    -- the residual chain has an entry at j+1 (lengths agree)
    have hlen := chainLenPreserved m sₘ s_l hsₘ hs_l hmin
    have hj1lt' : j + 1 < (MW.leadingChain (RSK.residual m)).val.segments.length := by
      omega
    have hw' : (MW.leadingChain (RSK.residual m)).val.segments[j + 1]? =
        some ((MW.leadingChain (RSK.residual m)).val.segments[j + 1]'hj1lt') :=
      List.getElem?_eq_getElem hj1lt'
    set w' := (MW.leadingChain (RSK.residual m)).val.segments[j + 1]'hj1lt' with hw'def
    obtain ⟨u', v', hsplitC', -⟩ :=
      split_of_getElem?_consecutive _ j wj w' hwj hw'
    obtain ⟨hll', hsucc'⟩ :=
      leadingChain_consecutive_link (RSK.residual m) u' v' wj w' hsplitC'
    have hw'a : w'.a = σ1.a := by omega
    refine ⟨w', hw', hw'a, ?_⟩
    -- end-monotonicity of the boundary partners: tⱼ.b < t'.b
    have hi_j_bk : i_j ∈ (bucket m (depth_of_segment m σj hσjm)).map (·.val) := by
      rw [hsplit_j]; simp
    obtain ⟨hi_j_m, hd_j⟩ := RSK.mem_bucket_depth m _ i_j hi_j_bk
    have hi'_bk : i' ∈ (bucket m (depth_of_segment m σ1 hσ1m)).map (·.val) := by
      rw [hsplit']; simp
    obtain ⟨hi'_m, hd'⟩ := RSK.mem_bucket_depth m _ i' hi'_bk
    have hddσ := ll_ne_depth m σj σ1 hσjm hσ1m hll
    rw [← hd_j] at hsplit_j
    rw [← hd'] at hsplit'
    have hmono : t_j.b < t'.b :=
      succ_end_mono m i_j i' t_j t' hi_j_m hi'_m l₁j l₂j hsplit_j l₁' l₂' hsplit'
        (by omega) (by omega)
    -- restore the σ-indexed splits for downstream uses
    rw [hd_j] at hsplit_j
    rw [hd'] at hsplit'
    -- the derived segment W_{j+1} of σ1's boundary lies in the residual
    obtain ⟨w1, hw1_bkres, hw1a, hw1b⟩ :=
      derived_mem_bucketResidual m _ i' t' l₁' l₂' hsplit'
    have hw1_mem : w1 ∈ (RSK.residual m).segments :=
      mem_residual_of_bucket m (RSK.depth_le_maxDepth m σ1 hσ1m) hw1_bkres
    -- W_{j+1} is a valid continuation of wⱼ
    have hlink1 : MW.chainLink wj w1 := by
      refine ⟨⟨by omega, by omega⟩, by omega⟩
    -- ≤: greedy minimality of w' against W_{j+1}
    have hle : w'.b ≤ t'.b := by
      have h := leadingChain_min_end (RSK.residual m) u' v' wj w' hsplitC'
        w1 hw1_mem hlink1
      omega
    -- ≥: fiber minimality of the continuation
    have hw'C : w' ∈ (MW.leadingChain (RSK.residual m)).val.segments := by
      rw [hsplitC']; simp
    have hw'_mem := MW.leadingChain_subset (RSK.residual m) w' hw'C
    have hge : t'.b ≤ w'.b :=
      residual_min_end_step m u v σj σ1 hsplitC hσjm hσ1m i_j t_j l₁j l₂j
        hsplit_j hia_j hta_j i' t' l₁' l₂' hsplit' hia' hta'
        w' hw'_mem (by omega) (by obtain ⟨-, h⟩ := hll'; omega)
    omega

/-! ## Derived-pair calculus at the coordinate level

The residual construction is analyzed through coordinate pairs `(a, b) : ℤ × ℤ`,
sidestepping well-formedness proofs. A fiber list (sorted with ascending begins and
descending ends) determines its derived pairs; their multiset is characterized by
three quantities: raw counts, begin-group tops, and begin-group transitions. -/

/-- Coordinate image of a segment. -/
private def segPair (s : Segment) : ℤ × ℤ := (s.a, s.b)

lemma segPair_inj : Function.Injective segPair := by
  intro s t h
  simp only [segPair, Prod.mk.injEq] at h
  exact seg_ext h.1 h.2

/-- The derived pairs of a fiber list, at the coordinate level. -/
private def derivedPairs (l : List Segment) : List (ℤ × ℤ) :=
  (l.zip l.tail).map (fun p => (p.1.a, p.2.b))

lemma derivedPairs_nil : derivedPairs [] = [] := rfl

lemma derivedPairs_single (x : Segment) : derivedPairs [x] = [] := rfl

lemma derivedPairs_cons_cons (x y : Segment) (l : List Segment) :
    derivedPairs (x :: y :: l) = (x.a, y.b) :: derivedPairs (y :: l) := rfl

/-- The bucket residual's coordinate pairs are the derived pairs of the bucket. -/
lemma bucketResidual_pairs (m : Multisegment) (d : ℕ) :
    (RSK.bucketResidual m d).map segPair = derivedPairs ((bucket m d).map (·.val)) := by
  apply List.ext_getElem
  · simp [RSK.bucketResidual, derivedPairs]
  · intro i h1 h2
    simp [RSK.bucketResidual, derivedPairs, segPair]
    exact ⟨rfl, rfl⟩

open Classical in
/-- Indicator: `w` is the top (maximal-end) element of its begin-group in `L`. -/
private noncomputable def topInd (L : List Segment) (w : ℤ × ℤ) : ℕ :=
  if ∃ x ∈ L, x.a = w.1 ∧ x.b = w.2 ∧ ∀ y ∈ L, y.a = w.1 → y.b ≤ x.b then 1 else 0

open Classical in
/-- Indicator: `w.1` is a begin of `L` and `w.2` is the top end of the next
begin-group. -/
private noncomputable def transInd (L : List Segment) (w : ℤ × ℤ) : ℕ :=
  if ∃ x ∈ L, x.a = w.1 ∧ ∃ z ∈ L, x.a < z.a ∧ z.b = w.2 ∧
      (∀ y ∈ L, x.a < y.a → z.a ≤ y.a) ∧ (∀ y ∈ L, y.a = z.a → y.b ≤ z.b) then 1 else 0


lemma topInd_nil (w : ℤ × ℤ) : topInd [] w = 0 := by
  simp [topInd]

lemma transInd_nil (w : ℤ × ℤ) : transInd [] w = 0 := by
  simp [transInd]

lemma topInd_eq_zero (L : List Segment) (w : ℤ × ℤ)
    (h : ∀ x ∈ L, x.a ≠ w.1) : topInd L w = 0 := by
  unfold topInd
  rw [if_neg]
  rintro ⟨x, hx, ha, -⟩
  exact h x hx ha

lemma transInd_eq_zero (L : List Segment) (w : ℤ × ℤ)
    (h : ∀ x ∈ L, x.a ≠ w.1) : transInd L w = 0 := by
  unfold transInd
  rw [if_neg]
  rintro ⟨x, hx, ha, -⟩
  exact h x hx ha

lemma count_map_segPair_eq_zero (L : List Segment) (w : ℤ × ℤ)
    (h : ∀ x ∈ L, x.a ≠ w.1) : (L.map segPair).count w = 0 := by
  rw [List.count_eq_zero]
  rintro hmem
  obtain ⟨x, hx, hfx⟩ := List.mem_map.mp hmem
  apply h x hx
  rw [← hfx]
  rfl

/-- Head-group top: with a dominating head, the group top of the head's begin is the
head itself. -/
lemma topInd_cons_eq (x : Segment) (rest : List Segment) (w : ℤ × ℤ)
    (hdom : ∀ z ∈ rest, x.a ≤ z.a ∧ z.b ≤ x.b) (hw1 : w.1 = x.a) :
    topInd (x :: rest) w = if w.2 = x.b then 1 else 0 := by
  unfold topInd
  by_cases hw2 : w.2 = x.b
  · rw [if_pos, if_pos hw2]
    refine ⟨x, List.mem_cons_self, hw1.symm, hw2.symm, ?_⟩
    intro y hy hya
    rcases List.mem_cons.mp hy with rfl | hyr
    · exact le_refl _
    · exact (hdom y hyr).2
  · rw [if_neg, if_neg hw2]
    rintro ⟨x', hx', ha', hb', hmax'⟩
    have hxle : x.b ≤ x'.b := hmax' x List.mem_cons_self hw1.symm
    have hxge : x'.b ≤ x.b := by
      rcases List.mem_cons.mp hx' with rfl | hr
      · exact le_refl _
      · exact (hdom x' hr).2
    omega

/-- Off-head-begin top: unaffected by consing a different-begin head. -/
lemma topInd_cons_ne (x : Segment) (rest : List Segment) (w : ℤ × ℤ)
    (hw1 : w.1 ≠ x.a) : topInd (x :: rest) w = topInd rest w := by
  unfold topInd
  by_cases hR : ∃ x' ∈ rest, x'.a = w.1 ∧ x'.b = w.2 ∧ ∀ y ∈ rest, y.a = w.1 → y.b ≤ x'.b
  · rw [if_pos, if_pos hR]
    obtain ⟨x', hx', ha', hb', hmax'⟩ := hR
    refine ⟨x', List.mem_cons_of_mem _ hx', ha', hb', ?_⟩
    intro y hy hya
    rcases List.mem_cons.mp hy with rfl | hyr
    · exact absurd hya.symm hw1
    · exact hmax' y hyr hya
  · rw [if_neg, if_neg hR]
    rintro ⟨x', hx', ha', hb', hmax'⟩
    rcases List.mem_cons.mp hx' with rfl | hr
    · exact hw1 ha'.symm
    · exact hR ⟨x', hr, ha', hb', fun y hy hya => hmax' y (List.mem_cons_of_mem _ hy) hya⟩

/-- Off-head-begin transitions: unaffected by consing a minimal-begin head. -/
lemma transInd_cons_ne (x : Segment) (rest : List Segment) (w : ℤ × ℤ)
    (hdom : ∀ z ∈ rest, x.a ≤ z.a ∧ z.b ≤ x.b) (hw1 : w.1 ≠ x.a) :
    transInd (x :: rest) w = transInd rest w := by
  unfold transInd
  by_cases hR : ∃ x' ∈ rest, x'.a = w.1 ∧ ∃ z ∈ rest, x'.a < z.a ∧ z.b = w.2 ∧
      (∀ y ∈ rest, x'.a < y.a → z.a ≤ y.a) ∧ (∀ y ∈ rest, y.a = z.a → y.b ≤ z.b)
  · rw [if_pos, if_pos hR]
    obtain ⟨x', hx', ha', z, hz, hlt, hzb, hmin, hmax⟩ := hR
    refine ⟨x', List.mem_cons_of_mem _ hx', ha', z, List.mem_cons_of_mem _ hz,
      hlt, hzb, ?_, ?_⟩
    · intro y hy hya
      rcases List.mem_cons.mp hy with rfl | hyr
      · have := (hdom x' hx').1; omega
      · exact hmin y hyr hya
    · intro y hy hya
      rcases List.mem_cons.mp hy with rfl | hyr
      · exfalso; have := (hdom x' hx').1; omega
      · exact hmax y hyr hya
  · rw [if_neg, if_neg hR]
    rintro ⟨x', hx', ha', z, hz, hlt, hzb, hmin, hmax⟩
    rcases List.mem_cons.mp hx' with rfl | hr
    · exact hw1 ha'.symm
    · have hzr : z ∈ rest := by
        rcases List.mem_cons.mp hz with rfl | h
        · exfalso; have := (hdom x' hr).1; omega
        · exact h
      exact hR ⟨x', hr, ha', z, hzr, hlt, hzb,
        fun y hy hya => hmin y (List.mem_cons_of_mem _ hy) hya,
        fun y hy hya => hmax y (List.mem_cons_of_mem _ hy) hya⟩

/-- Same-begin join: consing a head into its own begin-group leaves transitions
unchanged. -/
lemma transInd_cons_join (x y : Segment) (rest' : List Segment) (w : ℤ × ℤ)
    (hdom : ∀ z ∈ y :: rest', x.a ≤ z.a ∧ z.b ≤ x.b) (hxy : x.a = y.a)
    (hw1 : w.1 = x.a) :
    transInd (x :: y :: rest') w = transInd (y :: rest') w := by
  unfold transInd
  by_cases hR : ∃ x' ∈ y :: rest', x'.a = w.1 ∧ ∃ z ∈ y :: rest', x'.a < z.a ∧ z.b = w.2 ∧
      (∀ y' ∈ y :: rest', x'.a < y'.a → z.a ≤ y'.a) ∧ (∀ y' ∈ y :: rest', y'.a = z.a → y'.b ≤ z.b)
  · rw [if_pos, if_pos hR]
    obtain ⟨x', hx', ha', z, hz, hlt, hzb, hmin, hmax⟩ := hR
    refine ⟨x', List.mem_cons_of_mem _ hx', ha', z, List.mem_cons_of_mem _ hz,
      hlt, hzb, ?_, ?_⟩
    · intro y' hy' hya
      rcases List.mem_cons.mp hy' with rfl | hyr
      · omega
      · exact hmin y' hyr hya
    · intro y' hy' hya
      rcases List.mem_cons.mp hy' with rfl | hyr
      · exfalso; omega
      · exact hmax y' hyr hya
  · rw [if_neg, if_neg hR]
    rintro ⟨x', hx', ha', z, hz, hlt, hzb, hmin, hmax⟩
    have hzr : z ∈ y :: rest' := by
      rcases List.mem_cons.mp hz with rfl | h
      · exfalso; omega
      · exact h
    rcases List.mem_cons.mp hx' with rfl | hr
    · -- replace the head source by `y` (same begin)
      exact hR ⟨y, List.mem_cons_self, by omega, z, hzr, by omega, hzb,
        fun y' hy' hya => hmin y' (List.mem_cons_of_mem _ hy') (by omega),
        fun y' hy' hya => hmax y' (List.mem_cons_of_mem _ hy') hya⟩
    · exact hR ⟨x', hr, ha', z, hzr, hlt, hzb,
        fun y' hy' hya => hmin y' (List.mem_cons_of_mem _ hy') hya,
        fun y' hy' hya => hmax y' (List.mem_cons_of_mem _ hy') hya⟩

/-- New-group head: the head's transition targets the old head, which tops its group. -/
lemma transInd_cons_new (x y : Segment) (rest' : List Segment) (w : ℤ × ℤ)
    (hdom : ∀ z ∈ y :: rest', x.a ≤ z.a ∧ z.b ≤ x.b) (hxy : x.a < y.a)
    (hdom' : ∀ z ∈ rest', y.a ≤ z.a ∧ z.b ≤ y.b) (hw1 : w.1 = x.a) :
    transInd (x :: y :: rest') w = if w.2 = y.b then 1 else 0 := by
  unfold transInd
  by_cases hw2 : w.2 = y.b
  · rw [if_pos, if_pos hw2]
    refine ⟨x, List.mem_cons_self, hw1.symm, y,
      List.mem_cons_of_mem _ List.mem_cons_self, hxy, hw2.symm, ?_, ?_⟩
    · intro y' hy' hya
      rcases List.mem_cons.mp hy' with rfl | hyr
      · omega
      · rcases List.mem_cons.mp hyr with rfl | hyr'
        · exact le_refl _
        · exact (hdom' y' hyr').1
    · intro y' hy' hya
      rcases List.mem_cons.mp hy' with rfl | hyr
      · omega
      · rcases List.mem_cons.mp hyr with rfl | hyr'
        · exact le_refl _
        · exact (hdom' y' hyr').2
  · rw [if_neg, if_neg hw2]
    rintro ⟨x', hx', ha', z, hz, hlt, hzb, hmin, hmax⟩
    -- the source has the head's begin; the target must be `y`'s value-top
    have hx'a : x'.a = x.a := by omega
    have hzy : z ∈ y :: rest' := by
      rcases List.mem_cons.mp hz with rfl | h
      · exfalso; omega
      · exact h
    have hza : z.a = y.a := by
      have h1 : z.a ≤ y.a := hmin y (List.mem_cons_of_mem _ List.mem_cons_self) (by omega)
      rcases List.mem_cons.mp hzy with rfl | hzr
      · rfl
      · have := (hdom' z hzr).1; omega
    have hzb' : z.b = y.b := by
      have h1 : y.b ≤ z.b := hmax y (List.mem_cons_of_mem _ List.mem_cons_self) hza.symm
      rcases List.mem_cons.mp hzy with rfl | hzr
      · rfl
      · have := (hdom' z hzr).2; omega
    omega

/-- `List.count` on coordinate pairs, cons form with a propositional `if`. -/
lemma count_pairs_cons (p : ℤ × ℤ) (l : List (ℤ × ℤ)) (w : ℤ × ℤ) :
    (p :: l).count w = l.count w + if w = p then 1 else 0 := by
  rw [List.count_cons]
  congr 1
  by_cases h : p = w
  · rw [if_pos (beq_iff_eq.mpr h), if_pos h.symm]
  · rw [if_neg (fun hb => h (beq_iff_eq.mp hb)), if_neg (fun h' => h h'.symm)]

lemma transInd_single (x : Segment) (w : ℤ × ℤ) : transInd [x] w = 0 := by
  unfold transInd
  rw [if_neg]
  rintro ⟨x', hx', -, z, hz, hlt, -⟩
  rw [List.mem_singleton] at hx' hz
  subst hx'
  subst hz
  exact lt_irrefl _ hlt

lemma topInd_single (x : Segment) (w : ℤ × ℤ) :
    topInd [x] w = if w = segPair x then 1 else 0 := by
  unfold topInd
  by_cases h : w = segPair x
  · have hP : ∃ x' ∈ [x], x'.a = w.1 ∧ x'.b = w.2 ∧ ∀ y ∈ [x], y.a = w.1 → y.b ≤ x'.b :=
      ⟨x, List.mem_singleton_self x, by rw [h]; rfl, by rw [h]; rfl,
        fun y hy _ => by rw [List.mem_singleton] at hy; rw [hy]⟩
    rw [if_pos hP, if_pos h]
  · rw [if_neg ?_, if_neg h]
    rintro ⟨x', hx', ha, hb, -⟩
    rw [List.mem_singleton] at hx'
    subst hx'
    apply h
    have hw : w = (w.1, w.2) := rfl
    rw [hw, ← ha, ← hb]
    rfl

/-- **Derived-pair count characterization**: for a nested-sorted fiber list, the
multiset of derived pairs is the fiber multiset minus each begin-group's top plus each
begin-group transition target. -/
lemma derivedPairs_count (w : ℤ × ℤ) : ∀ (L : List Segment),
    L.Pairwise (fun s t => s.a ≤ t.a ∧ t.b ≤ s.b) →
    (derivedPairs L).count w + topInd L w =
      (L.map segPair).count w + transInd L w := by
  intro L
  induction L with
  | nil => intro _; simp [derivedPairs_nil, topInd_nil, transInd_nil]
  | cons x rest ih =>
    intro hs
    obtain ⟨hdom, hs'⟩ := List.pairwise_cons.mp hs
    cases rest with
    | nil =>
      rw [derivedPairs_single, topInd_single, transInd_single,
        show List.map segPair [x] = [segPair x] from rfl, count_pairs_cons, List.count_nil]
      split_ifs <;> omega
    | cons y rest' =>
      have ihy := ih hs'
      obtain ⟨hdom', hs''⟩ := List.pairwise_cons.mp hs'
      rw [derivedPairs_cons_cons, count_pairs_cons,
        show List.map segPair (x :: y :: rest') = segPair x :: List.map segPair (y :: rest')
          from rfl, count_pairs_cons]
      have hxya : x.a ≤ y.a := (hdom y List.mem_cons_self).1
      by_cases hw1 : w.1 = x.a
      · have e1 : (w = (x.a, y.b)) ↔ (w.2 = y.b) := by
          constructor
          · intro h; rw [h]
          · intro h
            have hw : w = (w.1, w.2) := rfl
            rw [hw, hw1, h]
        have e2 : (w = segPair x) ↔ (w.2 = x.b) := by
          constructor
          · intro h; rw [h]; rfl
          · intro h
            have hw : w = (w.1, w.2) := rfl
            rw [hw, hw1, h]; rfl
        rcases eq_or_lt_of_le hxya with hxy | hxy
        · -- join: x joins y's begin-group
          rw [topInd_cons_eq x (y :: rest') w hdom hw1,
            transInd_cons_join x y rest' w hdom hxy hw1]
          rw [topInd_cons_eq y rest' w hdom' (by omega)] at ihy
          simp only [e1, e2]
          split_ifs at ihy ⊢ <;> omega
        · -- new group headed by x
          rw [topInd_cons_eq x (y :: rest') w hdom hw1,
            transInd_cons_new x y rest' w hdom hxy hdom' hw1]
          have hz : ∀ x' ∈ y :: rest', x'.a ≠ w.1 := by
            intro x' hx'
            rcases List.mem_cons.mp hx' with rfl | hr
            · omega
            · have := (hdom' x' hr).1; omega
          rw [topInd_eq_zero _ w hz, transInd_eq_zero _ w hz,
            count_map_segPair_eq_zero _ w hz] at ihy
          rw [count_map_segPair_eq_zero _ w hz]
          simp only [e1, e2]
          split_ifs <;> omega
      · -- w's begin differs from the head: everything passes through
        rw [topInd_cons_ne x (y :: rest') w hw1, transInd_cons_ne x (y :: rest') w hdom hw1]
        rw [if_neg (by intro h; apply hw1; rw [h]),
          if_neg (by intro h; apply hw1; rw [h]; rfl)]
        omega

/-! ## Fiber and residual counts -/

/-- Count of a value in a bucket: its full multiplicity if it lives at that depth. -/
lemma count_bucket_of_depth (M : Multisegment) (d : ℕ) (x : Segment)
    (hx : x ∈ M.segments) (hd : depth_of_segment M x hx = d) :
    ((bucket M d).map (·.val)).count x = M.segments.count x := by
  have hperm : ((bucket M d).map (·.val)).Perm
      ((M.segments.attach.filter fun z =>
        depth_of_segment M z.val z.property = d).map (·.val)) := by
    apply List.Perm.map
    unfold bucket
    exact List.perm_insertionSort _ _
  rw [hperm.count_eq]
  rw [show x = (⟨x, hx⟩ : {s : Segment // s ∈ M.segments}).val from rfl,
    List.count_map_of_injective _ _ Subtype.coe_injective]
  rw [List.count_filter (by simp [hd])]
  exact List.count_attach

/-- Count of a value in a bucket at the wrong depth (or absent from `M`): zero. -/
lemma count_bucket_of_ne (M : Multisegment) (d : ℕ) (x : Segment)
    (h : ¬ ∃ hx : x ∈ M.segments, depth_of_segment M x hx = d) :
    ((bucket M d).map (·.val)).count x = 0 := by
  rw [List.count_eq_zero]
  intro hmem
  exact h (RSK.mem_bucket_depth M d x hmem)

/-- `makeResidual` counts split into the erase-fold part and the starred part. -/
lemma count_makeResidual (m : Multisegment) (Cl : List Segment) (x : Segment) :
    (MW.makeResidual m Cl).segments.count x =
      (Cl.foldl List.erase m.segments).count x +
        (Cl.filterMap MW.segmentResidual).count x := by
  simp only [MW.makeResidual]
  rw [(List.perm_insertionSort (· ≤ ·) _).count_eq, List.count_append]

/-- Erase-fold counts: for pairwise-distinct erased values each present in the base
list, exactly one copy of each is removed. -/
lemma count_foldl_erase : ∀ (Cl l : List Segment),
    Cl.Pairwise (· ≠ ·) → (∀ c ∈ Cl, c ∈ l) → ∀ (x : Segment),
    (Cl.foldl List.erase l).count x + (if x ∈ Cl then 1 else 0) = l.count x := by
  intro Cl
  induction Cl with
  | nil => intro l _ _ x; simp
  | cons c cs ih =>
    intro l hnd hsub x
    obtain ⟨hne, hnd'⟩ := List.pairwise_cons.mp hnd
    rw [List.foldl_cons]
    have hsub' : ∀ c' ∈ cs, c' ∈ l.erase c := by
      intro c' hc'
      exact (List.mem_erase_of_ne (fun h => hne c' hc' h.symm)).mpr
        (hsub c' (List.mem_cons_of_mem _ hc'))
    have hix := ih (l.erase c) hnd' hsub' x
    by_cases hxc : x = c
    · subst hxc
      rw [if_pos List.mem_cons_self]
      have hxcs : x ∉ cs := fun h => hne x h rfl
      rw [if_neg hxcs] at hix
      have hcount := List.count_erase_self (a := x) (l := l)
      have hpos : 0 < l.count x := List.count_pos_iff.mpr (hsub x List.mem_cons_self)
      omega
    · have hxl : (l.erase c).count x = l.count x := by
        rw [List.count_erase_of_ne hxc]
      by_cases hxcs : x ∈ cs
      · rw [if_pos (List.mem_cons_of_mem _ hxcs)]
        rw [if_pos hxcs] at hix
        omega
      · rw [if_neg (by simp [hxc, hxcs])]
        rw [if_neg hxcs] at hix
        omega


/-- `List.count` on segments, cons form with a propositional `if`. -/
lemma count_seg_cons (p : Segment) (l : List Segment) (x : Segment) :
    (p :: l).count x = l.count x + if x = p then 1 else 0 := by
  rw [List.count_cons]
  congr 1
  by_cases h : p = x
  · rw [if_pos (beq_iff_eq.mpr h), if_pos h.symm]
  · rw [if_neg (fun hb => h (beq_iff_eq.mp hb)), if_neg (fun h' => h h'.symm)]

/-- Counts in the starred list: for chain lists with strictly increasing begins, each
value occurs at most once, matching the unique source. -/
lemma count_filterMap_residual : ∀ (Cl : List Segment),
    Cl.Pairwise (fun s t => s.a < t.a) → ∀ (x : Segment),
    (Cl.filterMap MW.segmentResidual).count x =
      if ∃ σ ∈ Cl, σ.a < σ.b ∧ x.a = σ.a + 1 ∧ x.b = σ.b then 1 else 0 := by
  intro Cl
  induction Cl with
  | nil => intro _ x; simp
  | cons c cs ih =>
    intro hp x
    obtain ⟨hlt, hp'⟩ := List.pairwise_cons.mp hp
    have hix := ih hp' x
    by_cases hcs : c.a < c.b
    · rw [List.filterMap_cons_some (segmentResidual_eq c hcs), count_seg_cons]
      by_cases hxc : x = (⟨⟨c.a + 1, c.b⟩, by omega⟩ : Segment)
      · have hxa : x.a = c.a + 1 := by
          have h := congrArg Segment.a hxc
          simpa using h
        have hxb : x.b = c.b := by
          have h := congrArg Segment.b hxc
          simpa using h
        rw [if_pos hxc, if_pos ⟨c, List.mem_cons_self, hcs, hxa, hxb⟩]
        have hnone : ¬ ∃ σ ∈ cs, σ.a < σ.b ∧ x.a = σ.a + 1 ∧ x.b = σ.b := by
          rintro ⟨σ, hσ, -, ha, -⟩
          have := hlt σ hσ
          omega
        rw [if_neg hnone] at hix
        omega
      · rw [if_neg hxc]
        have hiff : (∃ σ ∈ c :: cs, σ.a < σ.b ∧ x.a = σ.a + 1 ∧ x.b = σ.b) ↔
            (∃ σ ∈ cs, σ.a < σ.b ∧ x.a = σ.a + 1 ∧ x.b = σ.b) := by
          constructor
          · rintro ⟨σ, hσ, hσs, ha, hb⟩
            rcases List.mem_cons.mp hσ with rfl | hr
            · exfalso
              exact hxc (seg_ext (by simpa using ha) (by simpa using hb))
            · exact ⟨σ, hr, hσs, ha, hb⟩
          · rintro ⟨σ, hσ, hσs, ha, hb⟩
            exact ⟨σ, List.mem_cons_of_mem _ hσ, hσs, ha, hb⟩
        rw [hix]
        by_cases hQ : ∃ σ ∈ cs, σ.a < σ.b ∧ x.a = σ.a + 1 ∧ x.b = σ.b
        · rw [if_pos hQ, if_pos (hiff.mpr hQ)]
        · rw [if_neg hQ, if_neg (fun h => hQ (hiff.mp h))]
    · rw [List.filterMap_cons_none (by simp [MW.segmentResidual, hcs])]
      rw [hix]
      have hiff : (∃ σ ∈ c :: cs, σ.a < σ.b ∧ x.a = σ.a + 1 ∧ x.b = σ.b) ↔
          (∃ σ ∈ cs, σ.a < σ.b ∧ x.a = σ.a + 1 ∧ x.b = σ.b) := by
        constructor
        · rintro ⟨σ, hσ, hσs, ha, hb⟩
          rcases List.mem_cons.mp hσ with rfl | hr
          · exact absurd hσs hcs
          · exact ⟨σ, hr, hσs, ha, hb⟩
        · rintro ⟨σ, hσ, hσs, ha, hb⟩
          exact ⟨σ, List.mem_cons_of_mem _ hσ, hσs, ha, hb⟩
      by_cases hQ : ∃ σ ∈ cs, σ.a < σ.b ∧ x.a = σ.a + 1 ∧ x.b = σ.b
      · rw [if_pos hQ, if_pos (hiff.mpr hQ)]
      · rw [if_neg hQ, if_neg (fun h => hQ (hiff.mp h))]

/-! ## Depth classification of `m†`-elements -/

/-- **Non-special survivors keep their depth.** -/
lemma mdag_depth_survivor (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a)
    (x : Segment) (hxm : x ∈ m.segments)
    (hx' : x ∈ (MW.makeResidual m (MW.leadingChain m).val.segments).segments)
    (hns : ¬ ∃ σ ∈ (MW.leadingChain m).val.segments, ∃ hσm : σ ∈ m.segments,
      x.a = σ.a ∧ x.b < σ.b ∧ depth_of_segment m x hxm = depth_of_segment m σ hσm) :
    depth_of_segment (MW.makeResidual m (MW.leadingChain m).val.segments) x hx'
      = depth_of_segment m x hxm := by
  have hub := (mdag_depth_bound m sₘ s_l hsₘ hs_l hmin _).1 x hxm hx' rfl
  have hle : depth_of_segment (MW.makeResidual m (MW.leadingChain m).val.segments) x hx'
      ≤ depth_of_segment m x hxm := by
    rcases Nat.lt_or_ge (depth_of_segment (MW.makeResidual m
      (MW.leadingChain m).val.segments) x hx') (depth_of_segment m x hxm + 1) with h | h
    · omega
    · exfalso
      exact hns (hub.2 (by omega))
  by_cases hxC : x ∈ (MW.leadingChain m).val.segments
  · -- chain value: bound below through its starred copy
    have hnd := chain_seg_nondegenerate m sₘ s_l hsₘ hs_l hmin x hxC
    have hstep : x.a + 1 ≤ x.b := by omega
    have hz' := starred_mem_mdag m (MW.leadingChain m).val.segments x hxC hnd
    have h2 := depth_mdag_ge_inC m sₘ s_l hsₘ hs_l hmin x hxC
      (⟨⟨x.a + 1, x.b⟩, hstep⟩ : Segment) rfl rfl hz' hxm
    have h3 := depth_le_of_coord_le (MW.makeResidual m (MW.leadingChain m).val.segments)
      x (⟨⟨x.a + 1, x.b⟩, hstep⟩ : Segment) hx' hz'
      (by show x.a ≤ x.a + 1; omega) (by show x.b ≤ x.b; omega)
    omega
  · have := depth_mdag_ge_notC m sₘ s_l hsₘ hs_l hmin x hxm hxC hx'
    omega

/-- **Starred values sit exactly at their source's depth.** -/
lemma mdag_depth_starred (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a)
    (σ : Segment) (hσC : σ ∈ (MW.leadingChain m).val.segments) (hσm : σ ∈ m.segments)
    (hstep : σ.a + 1 ≤ σ.b)
    (hy' : (⟨⟨σ.a + 1, σ.b⟩, hstep⟩ : Segment)
      ∈ (MW.makeResidual m (MW.leadingChain m).val.segments).segments) :
    depth_of_segment (MW.makeResidual m (MW.leadingChain m).val.segments)
      (⟨⟨σ.a + 1, σ.b⟩, hstep⟩ : Segment) hy' = depth_of_segment m σ hσm :=
  le_antisymm
    ((mdag_depth_bound m sₘ s_l hsₘ hs_l hmin _).2 σ hσC hσm
      (⟨⟨σ.a + 1, σ.b⟩, hstep⟩ : Segment) rfl rfl hy' rfl)
    (depth_mdag_ge_inC m sₘ s_l hsₘ hs_l hmin σ hσC
      (⟨⟨σ.a + 1, σ.b⟩, hstep⟩ : Segment) rfl rfl hy' hσm)

/-- No segment is special with the chain head as witness. -/
lemma no_special_head (m : Multisegment) (sₘ : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (y : Segment) (hym : y ∈ m.segments) (hya : y.a = sₘ.a) (hyb : y.b < sₘ.b) :
    False := by
  have h1 : sₘ ≤ y := MW.head_le_mem m sₘ hsₘ y hym
  have h2 := MW.seg_b_le_of_le_of_a_eq h1 (by omega)
  omega

/-- Specials are bounded by their witness's chain predecessor. -/
lemma special_end_le_pred (m : Multisegment) (u v : List Segment) (σp σ' : Segment)
    (hsplit : (MW.leadingChain m).val.segments = u ++ σp :: σ' :: v)
    (y : Segment) (hym : y ∈ m.segments) (hya : y.a = σ'.a) (hyb : y.b < σ'.b) :
    y.b ≤ σp.b := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨-, hsucc⟩ := leadingChain_consecutive_link m u v σp σ' hsplit
  have hlink : MW.chainLink σp y := ⟨⟨by omega, hcon⟩, by omega⟩
  have := leadingChain_min_end m u v σp σ' hsplit y hym hlink
  omega

/-- Same-fiber elements one begin to the right end no later. -/
lemma fiber_succ_end_le (m : Multisegment) (σ : Segment) (hσm : σ ∈ m.segments)
    (y : Segment) (hym : y ∈ m.segments) (hya : y.a = σ.a + 1)
    (hdep : depth_of_segment m y hym = depth_of_segment m σ hσm) : y.b ≤ σ.b := by
  by_contra hcon
  push_neg at hcon
  have hll : σ ≪ y := ⟨by omega, hcon⟩
  have := ll_ne_depth m σ y hσm hym hll
  omega

/-- Beyond the boundary: every fiber element with begin past `i` sits at or after `t`,
in both coordinates. -/
lemma boundary_next_facts (m : Multisegment) (d : ℕ) (i t : Segment)
    (l₁ l₂ : List Segment)
    (hsplit : (bucket m d).map (·.val) = l₁ ++ i :: t :: l₂)
    (y : Segment) (hy : y ∈ (bucket m d).map (·.val)) (hya : i.a < y.a) :
    t.a ≤ y.a ∧ y.b ≤ t.b := by
  have hsorted := bucket_sorted m d
  have hnested := bucket_nested m d
  rw [hsplit] at hsorted hnested hy
  rcases List.mem_append.mp hy with h1 | h2
  · -- y before i: begins ascend, so y.a ≤ i.a — contradiction
    exfalso
    have := (List.pairwise_append.mp hsorted).2.2 y h1 i (by simp)
    omega
  · rcases List.mem_cons.mp h2 with rfl | h3
    · omega
    · rcases List.mem_cons.mp h3 with rfl | h4
      · exact ⟨le_refl _, le_refl _⟩
      · have hp := (List.pairwise_append.mp hnested).2.1
        have hty := (List.pairwise_cons.mp (List.pairwise_cons.mp hp).2).1 y h4
        have hps := (List.pairwise_append.mp hsorted).2.1
        have hty2 := (List.pairwise_cons.mp (List.pairwise_cons.mp hps).2).1 y h4
        exact ⟨hty2, hty.2⟩

/-! ## Chain structure helpers -/

/-- The leading chain is pairwise `≪`. -/
lemma leadingChain_pairwise_ll (m : Multisegment) :
    (MW.leadingChain m).val.segments.Pairwise (· ≪ ·) := by
  have h : (MW.leadingChain m).val.segments.IsChain (· ≪ ·) :=
    (MW.leadingChain m).property.imp (fun _ _ hab => hab.1)
  haveI : Trans (· ≪ · : Segment → Segment → Prop) (· ≪ ·) (· ≪ ·) :=
    ⟨fun h1 h2 => ll_trans _ _ _ h1 h2⟩
  exact h.pairwise

/-- The leading chain's begins strictly increase. -/
lemma leadingChain_begins_lt (m : Multisegment) :
    (MW.leadingChain m).val.segments.Pairwise (fun s t => s.a < t.a) :=
  (leadingChain_pairwise_ll m).imp (fun h => h.1)

/-- In a begins-increasing list, members are determined by their begin. -/
lemma begin_unique_of_pairwise_lt : ∀ (l : List Segment),
    l.Pairwise (fun s t => s.a < t.a) →
    ∀ x ∈ l, ∀ y ∈ l, x.a = y.a → x = y := by
  intro l
  induction l with
  | nil => intro _ x hx; simp at hx
  | cons c cs ih =>
    intro hp x hx y hy heq
    obtain ⟨hlt, hp'⟩ := List.pairwise_cons.mp hp
    rcases List.mem_cons.mp hx with rfl | hxr
    · rcases List.mem_cons.mp hy with rfl | hyr
      · rfl
      · exact absurd heq (by have := hlt y hyr; omega)
    · rcases List.mem_cons.mp hy with rfl | hyr
      · exact absurd heq (by have := hlt x hxr; omega)
      · exact ih hp' x hxr y hyr heq

/-- Two distinct members of a pairwise list are related one way or the other. -/
lemma pairwise_mem_rel {R : Segment → Segment → Prop} : ∀ (l : List Segment),
    l.Pairwise R → ∀ x ∈ l, ∀ y ∈ l, x ≠ y → R x y ∨ R y x := by
  intro l
  induction l with
  | nil => intro _ x hx; simp at hx
  | cons c cs ih =>
    intro hp x hx y hy hne
    obtain ⟨hrel, hp'⟩ := List.pairwise_cons.mp hp
    rcases List.mem_cons.mp hx with rfl | hxr
    · rcases List.mem_cons.mp hy with rfl | hyr
      · exact absurd rfl hne
      · exact Or.inl (hrel y hyr)
    · rcases List.mem_cons.mp hy with rfl | hyr
      · exact Or.inr (hrel x hxr)
      · exact ih hp' x hxr y hyr hne

/-- Distinct-begin chain members have distinct depths. -/
lemma chain_mem_depth_ne (m : Multisegment) (c σ : Segment)
    (hc : c ∈ (MW.leadingChain m).val.segments) (hσ : σ ∈ (MW.leadingChain m).val.segments)
    (hne : c.a ≠ σ.a) (hcm : c ∈ m.segments) (hσm : σ ∈ m.segments) :
    depth_of_segment m c hcm ≠ depth_of_segment m σ hσm := by
  have hvne : c ≠ σ := fun h => hne (by rw [h])
  rcases pairwise_mem_rel _ (leadingChain_pairwise_ll m) c hc σ hσ hvne with h | h
  · have := ll_ne_depth m c σ hcm hσm h; omega
  · have := ll_ne_depth m σ c hσm hcm h; omega

/-- A chain member strictly shallower than `σ` is at most as deep as its successor. -/
lemma chain_depth_between (m : Multisegment) (u v : List Segment) (σ σ' : Segment)
    (hsplit : (MW.leadingChain m).val.segments = u ++ σ :: σ' :: v)
    (c : Segment) (hc : c ∈ (MW.leadingChain m).val.segments)
    (hcm : c ∈ m.segments) (hσm : σ ∈ m.segments) (hσ'm : σ' ∈ m.segments)
    (hlt : depth_of_segment m c hcm < depth_of_segment m σ hσm) :
    depth_of_segment m c hcm ≤ depth_of_segment m σ' hσ'm := by
  have hCll := leadingChain_pairwise_ll m
  rw [hsplit] at hCll hc
  rcases List.mem_append.mp hc with h1 | h2
  · -- c precedes σ, so c ≪ σ and depth σ < depth c: contradiction
    exfalso
    have hll := (List.pairwise_append.mp hCll).2.2 c h1 σ (by simp)
    have := ll_ne_depth m c σ hcm hσm hll
    omega
  · rcases List.mem_cons.mp h2 with rfl | h3
    · omega
    · rcases List.mem_cons.mp h3 with rfl | h4
      · exact le_refl _
      · have hp := (List.pairwise_append.mp hCll).2.1
        have hll := (List.pairwise_cons.mp (List.pairwise_cons.mp hp).2).1 c h4
        have := ll_ne_depth m σ' c hσ'm hcm hll
        omega

/-- Full count formula for `m†`: one copy of each chain value is removed, one starred
copy of each non-singleton chain value is added. -/
lemma count_mdag_full (m : Multisegment) (x : Segment) :
    (MW.makeResidual m (MW.leadingChain m).val.segments).segments.count x
      + (if x ∈ (MW.leadingChain m).val.segments then 1 else 0)
      = m.segments.count x
      + (if ∃ σ ∈ (MW.leadingChain m).val.segments,
            σ.a < σ.b ∧ x.a = σ.a + 1 ∧ x.b = σ.b then 1 else 0) := by
  rw [count_makeResidual, count_filterMap_residual _ (leadingChain_begins_lt m) x]
  have hne : (MW.leadingChain m).val.segments.Pairwise (· ≠ ·) :=
    (leadingChain_begins_lt m).imp (fun h heq => by rw [heq] at h; omega)
  have hsub : ∀ c ∈ (MW.leadingChain m).val.segments, c ∈ m.segments :=
    fun c hc => MW.leadingChain_subset m c hc
  have := count_foldl_erase _ m.segments hne hsub x
  omega

/-- Bucket count when every copy of the value sits at depth `d`. -/
lemma bucket_count_eq_of_depth (M : Multisegment) (d : ℕ) (x : Segment)
    (h : ∀ hxm : x ∈ M.segments, depth_of_segment M x hxm = d) :
    ((bucket M d).map (·.val)).count x = M.segments.count x := by
  by_cases hmem : x ∈ M.segments
  · exact count_bucket_of_depth M d x hmem (h hmem)
  · rw [count_bucket_of_ne M d x (by rintro ⟨hxm, -⟩; exact hmem hxm),
      List.count_eq_zero.mpr hmem]

/-- Bucket count when the value never sits at depth `d`. -/
lemma bucket_count_eq_zero_of_depth_ne (M : Multisegment) (d : ℕ) (x : Segment)
    (h : ∀ hxm : x ∈ M.segments, depth_of_segment M x hxm ≠ d) :
    ((bucket M d).map (·.val)).count x = 0 :=
  count_bucket_of_ne M d x (by rintro ⟨hxm, hd⟩; exact h hxm hd)

/-- In a begins-increasing list, splits at a common element coincide. -/
lemma split_unique_of_pairwise_lt : ∀ (l : List Segment),
    l.Pairwise (fun s t => s.a < t.a) →
    ∀ (u v u' v' : List Segment) (σ : Segment),
    l = u ++ σ :: v → l = u' ++ σ :: v' → u = u' ∧ v = v' := by
  intro l
  induction l with
  | nil =>
    intro _ u v u' v' σ h1 _
    exact absurd h1.symm (by simp)
  | cons c cs ih =>
    intro hp u v u' v' σ h1 h2
    obtain ⟨hlt, hp'⟩ := List.pairwise_cons.mp hp
    cases u with
    | nil =>
      cases u' with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at h1 h2
        exact ⟨rfl, by rw [← h1.2, h2.2]⟩
      | cons c' u'' =>
        exfalso
        simp only [List.nil_append, List.cons.injEq] at h1
        simp only [List.cons_append, List.cons.injEq] at h2
        obtain ⟨rfl, -⟩ := h1
        obtain ⟨rfl, h2'⟩ := h2
        have hσ : c ∈ cs := by rw [h2']; simp
        have := hlt c hσ
        omega
    | cons c₀ u₀ =>
      cases u' with
      | nil =>
        exfalso
        simp only [List.nil_append, List.cons.injEq] at h2
        simp only [List.cons_append, List.cons.injEq] at h1
        obtain ⟨rfl, -⟩ := h2
        obtain ⟨rfl, h1'⟩ := h1
        have hσ : c ∈ cs := by rw [h1']; simp
        have := hlt c hσ
        omega
      | cons c₁ u₁ =>
        simp only [List.cons_append, List.cons.injEq] at h1 h2
        obtain ⟨rfl, h1'⟩ := h1
        obtain ⟨rfl, h2'⟩ := h2
        obtain ⟨hu, hv⟩ := ih hp' u₀ v u₁ v' σ h1' h2'
        exact ⟨by rw [hu], hv⟩

/-- Coordinate form of `mdag_depth_starred`. -/
lemma mdag_depth_starred' (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a)
    (c : Segment) (hcC : c ∈ (MW.leadingChain m).val.segments) (hcm : c ∈ m.segments)
    (hcnd : c.a < c.b)
    (x : Segment) (hxa : x.a = c.a + 1) (hxb : x.b = c.b)
    (hx' : x ∈ (MW.makeResidual m (MW.leadingChain m).val.segments).segments) :
    depth_of_segment (MW.makeResidual m (MW.leadingChain m).val.segments) x hx'
      = depth_of_segment m c hcm := by
  have hstep : c.a + 1 ≤ c.b := by omega
  have hxeq : x = (⟨⟨c.a + 1, c.b⟩, hstep⟩ : Segment) := by
    refine seg_ext ?_ ?_
    · rw [hxa]; rfl
    · rw [hxb]; rfl
  subst hxeq
  exact mdag_depth_starred m sₘ s_l hsₘ hs_l hmin c hcC hcm hstep hx'

/-- Depth respects value equality across membership proofs. -/
lemma depth_congr (m : Multisegment) (s t : Segment) (h : s = t)
    (hs : s ∈ m.segments) (ht : t ∈ m.segments) :
    depth_of_segment m s hs = depth_of_segment m t ht := by
  subst h
  rfl

/-- **Fiber-count transport at a chain fiber** (paper eqs. `sc2`/`sc3`, count form): at
`σ`'s fiber, `m†` loses one `σ`-copy and the specials of `σ`, and gains the starred copy
`⁻σ` together with the incoming specials of the successor `σ'`. -/
lemma fiber_count_chain_step (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a)
    (u v : List Segment) (σ σ' : Segment)
    (hsplit : (MW.leadingChain m).val.segments = u ++ σ :: σ' :: v)
    (hσm : σ ∈ m.segments) (hσ'm : σ' ∈ m.segments)
    (x : Segment) :
    ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
        (depth_of_segment m σ hσm)).map (·.val)).count x
      + (if x = σ then 1 else 0)
      + (if x.a = σ.a ∧ x.b < σ.b
         then ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count x else 0)
    = ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count x
      + (if x.a = σ.a + 1 ∧ x.b = σ.b then 1 else 0)
      + (if x.a = σ'.a ∧ x.b < σ'.b
         then ((bucket m (depth_of_segment m σ' hσ'm)).map (·.val)).count x else 0) := by
  classical
  have hσC : σ ∈ (MW.leadingChain m).val.segments := by rw [hsplit]; simp
  have hσ'C : σ' ∈ (MW.leadingChain m).val.segments := by rw [hsplit]; simp
  obtain ⟨hll, hsucc⟩ := leadingChain_consecutive_link m u v σ σ' hsplit
  obtain ⟨hlla, hllb⟩ := hll
  have hd'lt : depth_of_segment m σ' hσ'm < depth_of_segment m σ hσm :=
    ll_ne_depth m σ σ' hσm hσ'm ⟨hlla, hllb⟩
  have hnd : σ.a < σ.b := chain_seg_nondegenerate m sₘ s_l hsₘ hs_l hmin σ hσC
  have hcount := count_mdag_full m x
  have hBlt := leadingChain_begins_lt m
  have hCsub : ∀ c ∈ (MW.leadingChain m).val.segments, c ∈ m.segments :=
    fun c hc => MW.leadingChain_subset m c hc
  by_cases hx1 : x.a = σ.a
  · -- begin group of σ
    by_cases hx2 : x.b = σ.b
    · -- L1: x is the chain value σ itself
      have hxσ : x = σ := seg_ext hx1 hx2
      subst hxσ
      have hst : ¬ ∃ c ∈ (MW.leadingChain m).val.segments,
          c.a < c.b ∧ x.a = c.a + 1 ∧ x.b = c.b := by
        rintro ⟨c, hcC, -, hca, hcb⟩
        have hcne : c ≠ x := fun h => by rw [h] at hca; omega
        rcases pairwise_mem_rel _ (leadingChain_pairwise_ll m) c hcC x hσC hcne
          with h | h
        · obtain ⟨-, h2⟩ := h; omega
        · obtain ⟨h1, -⟩ := h; omega
      rw [if_pos hσC, if_neg hst] at hcount
      have hBm : ((bucket m (depth_of_segment m x hσm)).map (·.val)).count x
          = m.segments.count x :=
        bucket_count_eq_of_depth m _ x (fun _ => rfl)
      have hB : ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
          (depth_of_segment m x hσm)).map (·.val)).count x
          = (MW.makeResidual m (MW.leadingChain m).val.segments).segments.count x := by
        apply bucket_count_eq_of_depth
        intro hx'
        rw [mdag_depth_survivor m sₘ s_l hsₘ hs_l hmin x hσm hx' ?_]
        rintro ⟨σw, hσwC, hσwm, hwa, hwb, -⟩
        have := begin_unique_of_pairwise_lt _ hBlt σw hσwC x hσC (by omega)
        rw [this] at hwb
        omega
      rw [hB, hBm, if_pos rfl, if_neg (by rintro ⟨-, h⟩; omega),
        if_neg (by rintro ⟨h, -⟩; omega), if_neg (by rintro ⟨h, -⟩; omega)]
      omega
    · have hxnotC : x ∉ (MW.leadingChain m).val.segments := by
        intro hx
        have := begin_unique_of_pairwise_lt _ hBlt x hx σ hσC hx1
        have hb := congrArg Segment.b this
        simp only [] at hb
        omega
      by_cases hx3 : x.b < σ.b
      · -- specials of σ, or same-begin junk off the fiber
        by_cases hx4 : ∃ hxm : x ∈ m.segments,
            depth_of_segment m x hxm = depth_of_segment m σ hσm
        · -- L2: a genuine special of σ
          obtain ⟨hxm, hxd⟩ := hx4
          have hx' : x ∈ (MW.makeResidual m (MW.leadingChain m).val.segments).segments :=
            survivor_mem_mdag m _ x hxm hxnotC
          have hdep := special_moves_up m sₘ s_l hsₘ hs_l hmin x hxm hx'
            σ hσC hσm hx1 hx3 (by rw [hxd])
          have hB : ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
              (depth_of_segment m σ hσm)).map (·.val)).count x = 0 := by
            apply bucket_count_eq_zero_of_depth_ne
            intro hx'2
            have hpi : depth_of_segment (MW.makeResidual m
                (MW.leadingChain m).val.segments) x hx'2
                = depth_of_segment (MW.makeResidual m
                (MW.leadingChain m).val.segments) x hx' := rfl
            omega
          have hBm : ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count x
              = m.segments.count x :=
            bucket_count_eq_of_depth m _ x (fun hxm2 => by
              have : depth_of_segment m x hxm2 = depth_of_segment m x hxm := rfl
              omega)
          rw [hB, hBm, if_neg (fun h => by
              have := congrArg Segment.b h; simp only [] at this; omega),
            if_pos ⟨hx1, hx3⟩, if_neg (by rintro ⟨h, -⟩; omega),
            if_neg (by rintro ⟨h, -⟩; omega)]
          omega
        · -- L3: same-begin shorter value off the fiber
          have hB : ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
              (depth_of_segment m σ hσm)).map (·.val)).count x = 0 := by
            apply bucket_count_eq_zero_of_depth_ne
            intro hx'
            rcases mem_mdag_cases m _ x hx' with hxm | ⟨c, hcC, hcnd, hxa, hxb⟩
            · rw [mdag_depth_survivor m sₘ s_l hsₘ hs_l hmin x hxm hx' ?_]
              · exact fun h => hx4 ⟨hxm, h⟩
              · rintro ⟨σw, hσwC, hσwm, hwa, hwb, hwd⟩
                have heqw := begin_unique_of_pairwise_lt _ hBlt σw hσwC σ hσC (by omega)
                subst heqw
                exact hx4 ⟨hxm, hwd⟩
            · rw [mdag_depth_starred' m sₘ s_l hsₘ hs_l hmin c hcC (hCsub c hcC)
                hcnd x hxa hxb hx']
              exact chain_mem_depth_ne m c σ hcC hσC (by omega) (hCsub c hcC) hσm
          have hBm : ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count x = 0 :=
            bucket_count_eq_zero_of_depth_ne m _ x (fun hxm h => hx4 ⟨hxm, h⟩)
          rw [hB, hBm, if_neg (fun h => by
              have := congrArg Segment.b h; simp only [] at this; omega),
            if_pos ⟨hx1, hx3⟩, if_neg (by rintro ⟨h, -⟩; omega),
            if_neg (by rintro ⟨h, -⟩; omega)]
      · -- L4: same begin, larger end
        have hx4 : σ.b < x.b := by omega
        have hst : ¬ ∃ c ∈ (MW.leadingChain m).val.segments,
            c.a < c.b ∧ x.a = c.a + 1 ∧ x.b = c.b := by
          rintro ⟨c, hcC, -, hca, hcb⟩
          have hcne : c ≠ σ := fun h => by rw [h] at hca; omega
          rcases pairwise_mem_rel _ (leadingChain_pairwise_ll m) c hcC σ hσC hcne
            with h | h
          · obtain ⟨-, h2⟩ := h; omega
          · obtain ⟨h1, -⟩ := h; omega
        rw [if_neg hxnotC, if_neg hst] at hcount
        have hcert : ∀ (hxm : x ∈ m.segments),
            ¬ ∃ σw ∈ (MW.leadingChain m).val.segments, ∃ hσwm : σw ∈ m.segments,
              x.a = σw.a ∧ x.b < σw.b ∧
              depth_of_segment m x hxm = depth_of_segment m σw hσwm := by
          rintro hxm ⟨σw, hσwC, hσwm, hwa, hwb, -⟩
          have := begin_unique_of_pairwise_lt _ hBlt σw hσwC σ hσC (by omega)
          have hb := congrArg Segment.b this
          simp only [] at hb
          omega
        by_cases hf : ∃ hxm : x ∈ m.segments,
            depth_of_segment m x hxm = depth_of_segment m σ hσm
        · obtain ⟨hxm, hxd⟩ := hf
          have hBm : ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count x
              = m.segments.count x :=
            bucket_count_eq_of_depth m _ x (fun hxm2 => by
              have : depth_of_segment m x hxm2 = depth_of_segment m x hxm := rfl
              omega)
          have hx' : x ∈ (MW.makeResidual m (MW.leadingChain m).val.segments).segments :=
            survivor_mem_mdag m _ x hxm hxnotC
          have hB : ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
              (depth_of_segment m σ hσm)).map (·.val)).count x
              = (MW.makeResidual m (MW.leadingChain m).val.segments).segments.count x := by
            apply bucket_count_eq_of_depth
            intro hx'2
            rw [mdag_depth_survivor m sₘ s_l hsₘ hs_l hmin x hxm hx'2 (hcert hxm)]
            exact hxd
          rw [hB, hBm, if_neg (fun h => by
              have := congrArg Segment.b h; simp only [] at this; omega),
            if_neg (by rintro ⟨-, h⟩; omega), if_neg (by rintro ⟨h, -⟩; omega),
            if_neg (by rintro ⟨h, -⟩; omega)]
          omega
        · have hBm : ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count x = 0 :=
            bucket_count_eq_zero_of_depth_ne m _ x (fun hxm h => hf ⟨hxm, h⟩)
          have hB : ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
              (depth_of_segment m σ hσm)).map (·.val)).count x = 0 := by
            apply bucket_count_eq_zero_of_depth_ne
            intro hx'
            rcases mem_mdag_cases m _ x hx' with hxm | ⟨c, hcC, hcnd, hxa, hxb⟩
            · rw [mdag_depth_survivor m sₘ s_l hsₘ hs_l hmin x hxm hx' (hcert hxm)]
              exact fun h => hf ⟨hxm, h⟩
            · exact absurd ⟨c, hcC, hcnd, hxa, hxb⟩ hst
          rw [hB, hBm, if_neg (fun h => by
              have := congrArg Segment.b h; simp only [] at this; omega),
            if_neg (by rintro ⟨-, h⟩; omega), if_neg (by rintro ⟨h, -⟩; omega),
            if_neg (by rintro ⟨h, -⟩; omega)]
  · by_cases hx5 : x.a = σ.a + 1
    · -- begin group of σ'
      have hxσ'a : x.a = σ'.a := by omega
      by_cases hx6 : x.b = σ.b
      · -- L5a: the starred value ⁻σ
        have hxnotC : x ∉ (MW.leadingChain m).val.segments := by
          intro hx
          have := begin_unique_of_pairwise_lt _ hBlt x hx σ' hσ'C hxσ'a
          have hb := congrArg Segment.b this
          simp only [] at hb
          omega
        rw [if_neg hxnotC, if_pos ⟨σ, hσC, hnd, by omega, by omega⟩] at hcount
        have hx' : x ∈ (MW.makeResidual m (MW.leadingChain m).val.segments).segments := by
          rw [← List.count_pos_iff]
          omega
        have hB : ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
            (depth_of_segment m σ hσm)).map (·.val)).count x
            = (MW.makeResidual m (MW.leadingChain m).val.segments).segments.count x := by
          apply bucket_count_eq_of_depth
          intro hx'2
          exact mdag_depth_starred' m sₘ s_l hsₘ hs_l hmin σ hσC hσm hnd x
            (by omega) (by omega) hx'2
        have hsum : ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count x
            + ((bucket m (depth_of_segment m σ' hσ'm)).map (·.val)).count x
            = m.segments.count x := by
          by_cases hxm : x ∈ m.segments
          · have hge := depth_mdag_ge_notC m sₘ s_l hsₘ hs_l hmin x hxm hxnotC hx'
            have hub := (mdag_depth_bound m sₘ s_l hsₘ hs_l hmin _).1 x hxm hx' rfl
            have hdd := mdag_depth_starred' m sₘ s_l hsₘ hs_l hmin σ hσC hσm hnd x
              (by omega) (by omega) hx'
            rcases Nat.lt_or_ge (depth_of_segment m x hxm)
              (depth_of_segment m σ hσm) with hlt | hge2
            · -- one level down: forced special with witness σ'
              obtain ⟨σw, hσwC, hσwm, hwa, hwb, hwd⟩ := hub.2 (by omega)
              have hww := begin_unique_of_pairwise_lt _ hBlt σw hσwC σ' hσ'C (by omega)
              have hwd' : depth_of_segment m x hxm = depth_of_segment m σ' hσ'm :=
                hwd.trans (depth_congr m σw σ' hww hσwm hσ'm)
              have hB1 : ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count x
                  = 0 :=
                bucket_count_eq_zero_of_depth_ne m _ x (fun hxm2 h => by
                  have : depth_of_segment m x hxm2 = depth_of_segment m x hxm := rfl
                  omega)
              have hB2 : ((bucket m (depth_of_segment m σ' hσ'm)).map (·.val)).count x
                  = m.segments.count x :=
                bucket_count_eq_of_depth m _ x (fun hxm2 => by
                  have : depth_of_segment m x hxm2 = depth_of_segment m x hxm := rfl
                  omega)
              omega
            · have hxd : depth_of_segment m x hxm = depth_of_segment m σ hσm := by omega
              have hB1 : ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count x
                  = m.segments.count x :=
                bucket_count_eq_of_depth m _ x (fun hxm2 => by
                  have : depth_of_segment m x hxm2 = depth_of_segment m x hxm := rfl
                  omega)
              have hB2 : ((bucket m (depth_of_segment m σ' hσ'm)).map (·.val)).count x
                  = 0 :=
                bucket_count_eq_zero_of_depth_ne m _ x (fun hxm2 h => by
                  have : depth_of_segment m x hxm2 = depth_of_segment m x hxm := rfl
                  omega)
              omega
          · rw [bucket_count_eq_zero_of_depth_ne m _ x (fun hxm2 _ => hxm hxm2),
              bucket_count_eq_zero_of_depth_ne m _ x (fun hxm2 _ => hxm hxm2),
              List.count_eq_zero.mpr hxm]
        rw [hB, if_neg (fun h => by
            have := congrArg Segment.a h; simp only [] at this; omega),
          if_neg (by rintro ⟨h, -⟩; omega), if_pos ⟨hx5, hx6⟩,
          if_pos ⟨hxσ'a, by omega⟩]
        omega
      · by_cases hx7 : x.b = σ'.b
        · -- L5b: x is the chain value σ'
          have hxσ' : x = σ' := seg_ext hxσ'a hx7
          subst hxσ'
          have hst : ¬ ∃ c ∈ (MW.leadingChain m).val.segments,
              c.a < c.b ∧ x.a = c.a + 1 ∧ x.b = c.b := by
            rintro ⟨c, hcC, -, hca, hcb⟩
            have hcne : c ≠ x := fun h => by rw [h] at hca; omega
            rcases pairwise_mem_rel _ (leadingChain_pairwise_ll m) c hcC x hσ'C hcne
              with h | h
            · obtain ⟨-, h2⟩ := h; omega
            · obtain ⟨h1, -⟩ := h; omega
          rw [if_pos hσ'C, if_neg hst] at hcount
          have hB : ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
              (depth_of_segment m σ hσm)).map (·.val)).count x = 0 := by
            apply bucket_count_eq_zero_of_depth_ne
            intro hx'
            rw [mdag_depth_survivor m sₘ s_l hsₘ hs_l hmin x hσ'm hx' ?_]
            · omega
            · rintro ⟨σw, hσwC, hσwm, hwa, hwb, -⟩
              have := begin_unique_of_pairwise_lt _ hBlt σw hσwC x hσ'C (by omega)
              rw [this] at hwb
              omega
          have hBm : ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count x = 0 :=
            bucket_count_eq_zero_of_depth_ne m _ x (fun hxm2 h => by
              have : depth_of_segment m x hxm2 = depth_of_segment m x hσ'm := rfl
              omega)
          rw [hB, hBm, if_neg (fun h => by
              have := congrArg Segment.a h; simp only [] at this; omega),
            if_neg (by rintro ⟨h, -⟩; omega), if_neg (by rintro ⟨-, h⟩; omega),
            if_neg (by rintro ⟨-, h⟩; omega)]
        · -- L5c / L5d: other values in σ'’s begin group
          have hxnotC : x ∉ (MW.leadingChain m).val.segments := by
            intro hx
            have := begin_unique_of_pairwise_lt _ hBlt x hx σ' hσ'C hxσ'a
            have hb := congrArg Segment.b this
            simp only [] at hb
            omega
          have hst : ¬ ∃ c ∈ (MW.leadingChain m).val.segments,
              c.a < c.b ∧ x.a = c.a + 1 ∧ x.b = c.b := by
            rintro ⟨c, hcC, -, hca, hcb⟩
            have := begin_unique_of_pairwise_lt _ hBlt c hcC σ hσC (by omega)
            rw [this] at hcb
            omega
          rw [if_neg hxnotC, if_neg hst] at hcount
          by_cases hx8 : x.b < σ'.b
          · -- L5c
            by_cases hxm : x ∈ m.segments
            · by_cases he : depth_of_segment m x hxm = depth_of_segment m σ' hσ'm
              · -- special with witness σ': moves into σ's fiber
                have hx' : x ∈ (MW.makeResidual m
                    (MW.leadingChain m).val.segments).segments :=
                  survivor_mem_mdag m _ x hxm hxnotC
                have hdep := special_moves_up m sₘ s_l hsₘ hs_l hmin x hxm hx'
                  σ' hσ'C hσ'm hxσ'a hx8 (by rw [he])
                have hgap := special_witness_gap m sₘ s_l hsₘ hs_l hmin x hxm
                  σ' hσ'm hxσ'a hx8 (by rw [he]) u v σ hsplit hσm
                have hB : ((bucket (MW.makeResidual m
                    (MW.leadingChain m).val.segments)
                    (depth_of_segment m σ hσm)).map (·.val)).count x
                    = (MW.makeResidual m
                      (MW.leadingChain m).val.segments).segments.count x := by
                  apply bucket_count_eq_of_depth
                  intro hx'2
                  have hpi : depth_of_segment (MW.makeResidual m
                      (MW.leadingChain m).val.segments) x hx'2
                      = depth_of_segment (MW.makeResidual m
                      (MW.leadingChain m).val.segments) x hx' := rfl
                  omega
                have hB1 : ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count x
                    = 0 :=
                  bucket_count_eq_zero_of_depth_ne m _ x (fun hxm2 h => by
                    have : depth_of_segment m x hxm2 = depth_of_segment m x hxm := rfl
                    omega)
                have hB2 : ((bucket m
                    (depth_of_segment m σ' hσ'm)).map (·.val)).count x
                    = m.segments.count x :=
                  bucket_count_eq_of_depth m _ x (fun hxm2 => by
                    have : depth_of_segment m x hxm2 = depth_of_segment m x hxm := rfl
                    omega)
                rw [hB, hB1, if_neg (fun h => by
                    have := congrArg Segment.a h; simp only [] at this; omega),
                  if_neg (by rintro ⟨h, -⟩; omega), if_neg (by rintro ⟨-, h⟩; omega),
                  if_pos ⟨hxσ'a, hx8⟩, hB2]
                omega
              · -- non-special: depth preserved
                have hcert : ¬ ∃ σw ∈ (MW.leadingChain m).val.segments,
                    ∃ hσwm : σw ∈ m.segments, x.a = σw.a ∧ x.b < σw.b ∧
                    depth_of_segment m x hxm = depth_of_segment m σw hσwm := by
                  rintro ⟨σw, hσwC, hσwm, hwa, hwb, hwd⟩
                  have heqw := begin_unique_of_pairwise_lt _ hBlt σw hσwC σ' hσ'C (by omega)
                  subst heqw
                  exact he hwd
                have hx' : x ∈ (MW.makeResidual m
                    (MW.leadingChain m).val.segments).segments :=
                  survivor_mem_mdag m _ x hxm hxnotC
                have hdep := mdag_depth_survivor m sₘ s_l hsₘ hs_l hmin x hxm hx' hcert
                have hB2 : ((bucket m
                    (depth_of_segment m σ' hσ'm)).map (·.val)).count x = 0 :=
                  bucket_count_eq_zero_of_depth_ne m _ x (fun hxm2 h => by
                    have : depth_of_segment m x hxm2 = depth_of_segment m x hxm := rfl
                    omega)
                by_cases hed : depth_of_segment m x hxm = depth_of_segment m σ hσm
                · have hB : ((bucket (MW.makeResidual m
                      (MW.leadingChain m).val.segments)
                      (depth_of_segment m σ hσm)).map (·.val)).count x
                      = (MW.makeResidual m
                        (MW.leadingChain m).val.segments).segments.count x := by
                    apply bucket_count_eq_of_depth
                    intro hx'2
                    have hpi : depth_of_segment (MW.makeResidual m
                        (MW.leadingChain m).val.segments) x hx'2
                        = depth_of_segment (MW.makeResidual m
                        (MW.leadingChain m).val.segments) x hx' := rfl
                    omega
                  have hB1 : ((bucket m
                      (depth_of_segment m σ hσm)).map (·.val)).count x
                      = m.segments.count x :=
                    bucket_count_eq_of_depth m _ x (fun hxm2 => by
                      have : depth_of_segment m x hxm2 = depth_of_segment m x hxm := rfl
                      omega)
                  rw [hB, hB1, if_neg (fun h => by
                      have := congrArg Segment.a h; simp only [] at this; omega),
                    if_neg (by rintro ⟨h, -⟩; omega), if_neg (by rintro ⟨-, h⟩; omega),
                    if_pos ⟨hxσ'a, hx8⟩, hB2]
                  omega
                · have hB : ((bucket (MW.makeResidual m
                      (MW.leadingChain m).val.segments)
                      (depth_of_segment m σ hσm)).map (·.val)).count x = 0 := by
                    apply bucket_count_eq_zero_of_depth_ne
                    intro hx'2
                    have hpi : depth_of_segment (MW.makeResidual m
                        (MW.leadingChain m).val.segments) x hx'2
                        = depth_of_segment (MW.makeResidual m
                        (MW.leadingChain m).val.segments) x hx' := rfl
                    omega
                  have hB1 : ((bucket m
                      (depth_of_segment m σ hσm)).map (·.val)).count x = 0 :=
                    bucket_count_eq_zero_of_depth_ne m _ x (fun hxm2 h => by
                      have : depth_of_segment m x hxm2 = depth_of_segment m x hxm := rfl
                      omega)
                  rw [hB, hB1, if_neg (fun h => by
                      have := congrArg Segment.a h; simp only [] at this; omega),
                    if_neg (by rintro ⟨h, -⟩; omega), if_neg (by rintro ⟨-, h⟩; omega),
                    if_pos ⟨hxσ'a, hx8⟩, hB2]
            · -- x is not in m at all
              have hzero : m.segments.count x = 0 := List.count_eq_zero.mpr hxm
              have hB : ((bucket (MW.makeResidual m
                  (MW.leadingChain m).val.segments)
                  (depth_of_segment m σ hσm)).map (·.val)).count x = 0 := by
                apply bucket_count_eq_zero_of_depth_ne
                intro hx'
                have := List.count_pos_iff.mpr hx'
                omega
              rw [hB, bucket_count_eq_zero_of_depth_ne m _ x (fun hxm2 _ => hxm hxm2),
                bucket_count_eq_zero_of_depth_ne m _ x (fun hxm2 _ => hxm hxm2),
                if_neg (fun h => by
                  have := congrArg Segment.a h; simp only [] at this; omega),
                if_neg (by rintro ⟨h, -⟩; omega), if_neg (by rintro ⟨-, h⟩; omega)]
              simp
          · -- L5d: end beyond σ'
            have hx9 : σ'.b < x.b := by omega
            have hcert : ∀ (hxm : x ∈ m.segments),
                ¬ ∃ σw ∈ (MW.leadingChain m).val.segments, ∃ hσwm : σw ∈ m.segments,
                  x.a = σw.a ∧ x.b < σw.b ∧
                  depth_of_segment m x hxm = depth_of_segment m σw hσwm := by
              rintro hxm ⟨σw, hσwC, hσwm, hwa, hwb, -⟩
              have := begin_unique_of_pairwise_lt _ hBlt σw hσwC σ' hσ'C (by omega)
              have hb := congrArg Segment.b this
              simp only [] at hb
              omega
            by_cases hf : ∃ hxm : x ∈ m.segments,
                depth_of_segment m x hxm = depth_of_segment m σ hσm
            · obtain ⟨hxm, hxd⟩ := hf
              have hx' : x ∈ (MW.makeResidual m
                  (MW.leadingChain m).val.segments).segments :=
                survivor_mem_mdag m _ x hxm hxnotC
              have hB : ((bucket (MW.makeResidual m
                  (MW.leadingChain m).val.segments)
                  (depth_of_segment m σ hσm)).map (·.val)).count x
                  = (MW.makeResidual m
                    (MW.leadingChain m).val.segments).segments.count x := by
                apply bucket_count_eq_of_depth
                intro hx'2
                rw [mdag_depth_survivor m sₘ s_l hsₘ hs_l hmin x hxm hx'2 (hcert hxm)]
                exact hxd
              have hB1 : ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count x
                  = m.segments.count x :=
                bucket_count_eq_of_depth m _ x (fun hxm2 => by
                  have : depth_of_segment m x hxm2 = depth_of_segment m x hxm := rfl
                  omega)
              rw [hB, hB1, if_neg (fun h => by
                  have := congrArg Segment.a h; simp only [] at this; omega),
                if_neg (by rintro ⟨-, h⟩; omega), if_neg (by rintro ⟨-, h⟩; omega),
                if_neg (by rintro ⟨-, h⟩; omega)]
              omega
            · have hB1 : ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count x
                  = 0 :=
                bucket_count_eq_zero_of_depth_ne m _ x (fun hxm h => hf ⟨hxm, h⟩)
              have hB : ((bucket (MW.makeResidual m
                  (MW.leadingChain m).val.segments)
                  (depth_of_segment m σ hσm)).map (·.val)).count x = 0 := by
                apply bucket_count_eq_zero_of_depth_ne
                intro hx'
                rcases mem_mdag_cases m _ x hx' with hxm | ⟨c, hcC, hcnd, hxa, hxb⟩
                · rw [mdag_depth_survivor m sₘ s_l hsₘ hs_l hmin x hxm hx' (hcert hxm)]
                  exact fun h => hf ⟨hxm, h⟩
                · exact absurd ⟨c, hcC, hcnd, hxa, hxb⟩ hst
              rw [hB, hB1, if_neg (fun h => by
                  have := congrArg Segment.a h; simp only [] at this; omega),
                if_neg (by rintro ⟨-, h⟩; omega), if_neg (by rintro ⟨-, h⟩; omega),
                if_neg (by rintro ⟨-, h⟩; omega)]
    · -- L6: begins outside both groups
      rw [if_neg (fun h => by
          have := congrArg Segment.a h; simp only [] at this; omega),
        if_neg (by rintro ⟨h, -⟩; omega), if_neg (by rintro ⟨h, -⟩; omega),
        if_neg (by rintro ⟨h, -⟩; omega)]
      have hgoal : ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
          (depth_of_segment m σ hσm)).map (·.val)).count x
          = ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count x := by
        by_cases hxC : x ∈ (MW.leadingChain m).val.segments
        · -- another chain value: wrong fiber on both sides
          have hxm := hCsub x hxC
          have hend : depth_of_segment m x hxm ≠ depth_of_segment m σ hσm :=
            chain_mem_depth_ne m x σ hxC hσC hx1 hxm hσm
          rw [bucket_count_eq_zero_of_depth_ne m _ x (fun hxm2 h => by
            have : depth_of_segment m x hxm2 = depth_of_segment m x hxm := rfl
            omega)]
          apply bucket_count_eq_zero_of_depth_ne
          intro hx'
          rw [mdag_depth_survivor m sₘ s_l hsₘ hs_l hmin x hxm hx' ?_]
          · exact hend
          · rintro ⟨σw, hσwC, hσwm, hwa, hwb, -⟩
            have := begin_unique_of_pairwise_lt _ hBlt σw hσwC x hxC (by omega)
            rw [this] at hwb
            omega
        · by_cases hstt : ∃ c ∈ (MW.leadingChain m).val.segments,
              c.a < c.b ∧ x.a = c.a + 1 ∧ x.b = c.b
          · -- another starred value: wrong fiber on both sides
            obtain ⟨c, hcC, hcnd, hxa, hxb⟩ := hstt
            have hcm := hCsub c hcC
            have hdc : depth_of_segment m c hcm ≠ depth_of_segment m σ hσm :=
              chain_mem_depth_ne m c σ hcC hσC (by omega) hcm hσm
            have hx' : x ∈ (MW.makeResidual m
                (MW.leadingChain m).val.segments).segments := by
              rw [← List.count_pos_iff]
              rw [if_neg hxC, if_pos ⟨c, hcC, hcnd, hxa, hxb⟩] at hcount
              omega
            have hdd := mdag_depth_starred' m sₘ s_l hsₘ hs_l hmin c hcC hcm hcnd
              x hxa hxb hx'
            have hB : ((bucket (MW.makeResidual m
                (MW.leadingChain m).val.segments)
                (depth_of_segment m σ hσm)).map (·.val)).count x = 0 := by
              apply bucket_count_eq_zero_of_depth_ne
              intro hx'2
              have hpi : depth_of_segment (MW.makeResidual m
                  (MW.leadingChain m).val.segments) x hx'2
                  = depth_of_segment (MW.makeResidual m
                  (MW.leadingChain m).val.segments) x hx' := rfl
              omega
            rw [hB]
            symm
            apply bucket_count_eq_zero_of_depth_ne
            intro hxm hxd
            -- a surviving copy pinned at depth d would force a chain begin at x.a
            have hge := depth_mdag_ge_notC m sₘ s_l hsₘ hs_l hmin x hxm hxC hx'
            have hub := (mdag_depth_bound m sₘ s_l hsₘ hs_l hmin _).1 x hxm hx' rfl
            obtain ⟨σw, hσwC, hσwm, hwa, hwb, hwd⟩ := hub.2 (by omega)
            have hwne : σw.a ≠ σ.a := by omega
            have := chain_mem_depth_ne m σw σ hσwC hσC hwne hσwm hσm
            omega
          · -- plain value
            rw [if_neg hxC, if_neg hstt] at hcount
            by_cases hxm : x ∈ m.segments
            · by_cases hsp : ∃ σw ∈ (MW.leadingChain m).val.segments,
                  ∃ hσwm : σw ∈ m.segments, x.a = σw.a ∧ x.b < σw.b ∧
                  depth_of_segment m x hxm = depth_of_segment m σw hσwm
              · -- special with a foreign witness: wrong fiber on both sides
                obtain ⟨σw, hσwC, hσwm, hwa, hwb, hwd⟩ := hsp
                have hwne : σw.a ≠ σ.a := by omega
                have hdw : depth_of_segment m σw hσwm ≠ depth_of_segment m σ hσm :=
                  chain_mem_depth_ne m σw σ hσwC hσC hwne hσwm hσm
                have hB1 : ((bucket m
                    (depth_of_segment m σ hσm)).map (·.val)).count x = 0 :=
                  bucket_count_eq_zero_of_depth_ne m _ x (fun hxm2 h => by
                    have : depth_of_segment m x hxm2 = depth_of_segment m x hxm := rfl
                    omega)
                rw [hB1]
                apply bucket_count_eq_zero_of_depth_ne
                intro hx'
                have hdep := special_moves_up m sₘ s_l hsₘ hs_l hmin x hxm hx'
                  σw hσwC hσwm hwa hwb hwd
                intro hcon
                -- the landing fiber would identify σw's predecessor with σ
                have hheadne : (MW.leadingChain m).val.segments.head? ≠ some σw := by
                  rw [MW.leadingChain_head m sₘ hsₘ]
                  intro h
                  have heq := Option.some.inj h
                  have ha := congrArg Segment.a heq
                  have hb := congrArg Segment.b heq
                  simp only [] at ha hb
                  exact no_special_head m sₘ hsₘ x hxm (by omega) (by omega)
                obtain ⟨u₂, σp, v₂, hsplit₂⟩ :=
                  exists_pred_split (MW.leadingChain m).val.segments σw hσwC hheadne
                have hσpC : σp ∈ (MW.leadingChain m).val.segments := by
                  rw [hsplit₂]; simp
                have hσpm := hCsub σp hσpC
                have hgap := special_witness_gap m sₘ s_l hsₘ hs_l hmin x hxm
                  σw hσwm hwa hwb hwd u₂ v₂ σp hsplit₂ hσpm
                have hpσ : σp = σ := by
                  by_contra hne
                  have hpa : σp.a ≠ σ.a := by
                    intro ha
                    exact hne (begin_unique_of_pairwise_lt _ hBlt σp hσpC σ hσC ha)
                  have := chain_mem_depth_ne m σp σ hσpC hσC hpa hσpm hσm
                  omega
                subst hpσ
                obtain ⟨-, hv⟩ := split_unique_of_pairwise_lt _ hBlt
                  u₂ (σw :: v₂) u (σ' :: v) σp hsplit₂ hsplit
                have hσwσ' : σw = σ' := by
                  have := List.head_eq_of_cons_eq hv
                  exact this
                rw [hσwσ'] at hwa
                omega
              · -- plain non-special: depth preserved, counts transport
                have hx' : x ∈ (MW.makeResidual m
                    (MW.leadingChain m).val.segments).segments :=
                  survivor_mem_mdag m _ x hxm hxC
                have hdep := mdag_depth_survivor m sₘ s_l hsₘ hs_l hmin x hxm hx' hsp
                by_cases hf : depth_of_segment m x hxm = depth_of_segment m σ hσm
                · rw [bucket_count_eq_of_depth m _ x (fun hxm2 => by
                    have : depth_of_segment m x hxm2 = depth_of_segment m x hxm := rfl
                    omega)]
                  rw [bucket_count_eq_of_depth _ _ x (fun hx'2 => by
                    have hpi : depth_of_segment (MW.makeResidual m
                        (MW.leadingChain m).val.segments) x hx'2
                        = depth_of_segment (MW.makeResidual m
                        (MW.leadingChain m).val.segments) x hx' := rfl
                    omega)]
                  omega
                · rw [bucket_count_eq_zero_of_depth_ne m _ x (fun hxm2 h => by
                    have : depth_of_segment m x hxm2 = depth_of_segment m x hxm := rfl
                    omega)]
                  apply bucket_count_eq_zero_of_depth_ne
                  intro hx'2
                  have hpi : depth_of_segment (MW.makeResidual m
                      (MW.leadingChain m).val.segments) x hx'2
                      = depth_of_segment (MW.makeResidual m
                      (MW.leadingChain m).val.segments) x hx' := rfl
                  omega
            · have hB : ((bucket (MW.makeResidual m
                  (MW.leadingChain m).val.segments)
                  (depth_of_segment m σ hσm)).map (·.val)).count x = 0 := by
                apply bucket_count_eq_zero_of_depth_ne
                intro hx'
                have := List.count_pos_iff.mpr hx'
                have hzero : m.segments.count x = 0 := List.count_eq_zero.mpr hxm
                omega
              rw [hB, bucket_count_eq_zero_of_depth_ne m _ x (fun hxm2 _ => hxm hxm2)]
      omega

/-- **Fiber-count transport at the last chain fiber**: as `fiber_count_chain_step`, but
the last chain element has no successor — nothing migrates in. -/
lemma fiber_count_chain_last (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a)
    (u : List Segment) (σ : Segment)
    (hsplit : (MW.leadingChain m).val.segments = u ++ [σ])
    (hσm : σ ∈ m.segments) (x : Segment) :
    ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
        (depth_of_segment m σ hσm)).map (·.val)).count x
      + (if x = σ then 1 else 0)
      + (if x.a = σ.a ∧ x.b < σ.b
         then ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count x else 0)
    = ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count x
      + (if x.a = σ.a + 1 ∧ x.b = σ.b then 1 else 0) := by
  classical
  have hσC : σ ∈ (MW.leadingChain m).val.segments := by rw [hsplit]; simp
  have hnd : σ.a < σ.b := chain_seg_nondegenerate m sₘ s_l hsₘ hs_l hmin σ hσC
  have hcount := count_mdag_full m x
  have hBlt := leadingChain_begins_lt m
  have hCsub : ∀ c ∈ (MW.leadingChain m).val.segments, c ∈ m.segments :=
    fun c hc => MW.leadingChain_subset m c hc
  -- the last chain element dominates in begin and has minimal depth
  have hlast : ∀ c ∈ (MW.leadingChain m).val.segments, c = σ ∨ (c ≪ σ) := by
    intro c hc
    have hCll := leadingChain_pairwise_ll m
    rw [hsplit] at hCll hc
    rcases List.mem_append.mp hc with h1 | h2
    · exact Or.inr ((List.pairwise_append.mp hCll).2.2 c h1 σ (by simp))
    · rw [List.mem_singleton] at h2
      exact Or.inl h2
  have hmaxa : ∀ c ∈ (MW.leadingChain m).val.segments, c.a ≤ σ.a := by
    intro c hc
    rcases hlast c hc with rfl | h
    · exact le_refl _
    · exact le_of_lt h.1
  by_cases hx1 : x.a = σ.a
  · by_cases hx2 : x.b = σ.b
    · -- x is the chain value σ itself
      have hxσ : x = σ := seg_ext hx1 hx2
      subst hxσ
      have hst : ¬ ∃ c ∈ (MW.leadingChain m).val.segments,
          c.a < c.b ∧ x.a = c.a + 1 ∧ x.b = c.b := by
        rintro ⟨c, hcC, -, hca, hcb⟩
        rcases hlast c hcC with rfl | h
        · omega
        · obtain ⟨-, h2⟩ := h; omega
      rw [if_pos hσC, if_neg hst] at hcount
      have hBm : ((bucket m (depth_of_segment m x hσm)).map (·.val)).count x
          = m.segments.count x :=
        bucket_count_eq_of_depth m _ x (fun _ => rfl)
      have hB : ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
          (depth_of_segment m x hσm)).map (·.val)).count x
          = (MW.makeResidual m (MW.leadingChain m).val.segments).segments.count x := by
        apply bucket_count_eq_of_depth
        intro hx'
        rw [mdag_depth_survivor m sₘ s_l hsₘ hs_l hmin x hσm hx' ?_]
        rintro ⟨σw, hσwC, hσwm, hwa, hwb, -⟩
        have := begin_unique_of_pairwise_lt _ hBlt σw hσwC x hσC (by omega)
        rw [this] at hwb
        omega
      rw [hB, hBm, if_pos rfl, if_neg (by rintro ⟨-, h⟩; omega),
        if_neg (by rintro ⟨h, -⟩; omega)]
      omega
    · have hxnotC : x ∉ (MW.leadingChain m).val.segments := by
        intro hx
        have := begin_unique_of_pairwise_lt _ hBlt x hx σ hσC hx1
        have hb := congrArg Segment.b this
        simp only [] at hb
        omega
      by_cases hx3 : x.b < σ.b
      · by_cases hx4 : ∃ hxm : x ∈ m.segments,
            depth_of_segment m x hxm = depth_of_segment m σ hσm
        · -- special of σ: leaves the fiber
          obtain ⟨hxm, hxd⟩ := hx4
          have hx' : x ∈ (MW.makeResidual m (MW.leadingChain m).val.segments).segments :=
            survivor_mem_mdag m _ x hxm hxnotC
          have hdep := special_moves_up m sₘ s_l hsₘ hs_l hmin x hxm hx'
            σ hσC hσm hx1 hx3 (by rw [hxd])
          have hB : ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
              (depth_of_segment m σ hσm)).map (·.val)).count x = 0 := by
            apply bucket_count_eq_zero_of_depth_ne
            intro hx'2
            have hpi : depth_of_segment (MW.makeResidual m
                (MW.leadingChain m).val.segments) x hx'2
                = depth_of_segment (MW.makeResidual m
                (MW.leadingChain m).val.segments) x hx' := rfl
            omega
          have hBm : ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count x
              = m.segments.count x :=
            bucket_count_eq_of_depth m _ x (fun hxm2 => by
              have : depth_of_segment m x hxm2 = depth_of_segment m x hxm := rfl
              omega)
          rw [hB, hBm, if_neg (fun h => by
              have := congrArg Segment.b h; simp only [] at this; omega),
            if_pos ⟨hx1, hx3⟩, if_neg (by rintro ⟨h, -⟩; omega)]
          omega
        · have hB : ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
              (depth_of_segment m σ hσm)).map (·.val)).count x = 0 := by
            apply bucket_count_eq_zero_of_depth_ne
            intro hx'
            rcases mem_mdag_cases m _ x hx' with hxm | ⟨c, hcC, hcnd, hxa, hxb⟩
            · rw [mdag_depth_survivor m sₘ s_l hsₘ hs_l hmin x hxm hx' ?_]
              · exact fun h => hx4 ⟨hxm, h⟩
              · rintro ⟨σw, hσwC, hσwm, hwa, hwb, hwd⟩
                have heqw := begin_unique_of_pairwise_lt _ hBlt σw hσwC σ hσC (by omega)
                subst heqw
                exact hx4 ⟨hxm, hwd⟩
            · rw [mdag_depth_starred' m sₘ s_l hsₘ hs_l hmin c hcC (hCsub c hcC)
                hcnd x hxa hxb hx']
              exact chain_mem_depth_ne m c σ hcC hσC (by omega) (hCsub c hcC) hσm
          have hBm : ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count x = 0 :=
            bucket_count_eq_zero_of_depth_ne m _ x (fun hxm h => hx4 ⟨hxm, h⟩)
          rw [hB, hBm, if_neg (fun h => by
              have := congrArg Segment.b h; simp only [] at this; omega),
            if_pos ⟨hx1, hx3⟩, if_neg (by rintro ⟨h, -⟩; omega)]
      · -- same begin, larger end
        have hx4 : σ.b < x.b := by omega
        have hst : ¬ ∃ c ∈ (MW.leadingChain m).val.segments,
            c.a < c.b ∧ x.a = c.a + 1 ∧ x.b = c.b := by
          rintro ⟨c, hcC, -, hca, hcb⟩
          rcases hlast c hcC with rfl | h
          · omega
          · obtain ⟨-, h2⟩ := h; omega
        rw [if_neg hxnotC, if_neg hst] at hcount
        have hcert : ∀ (hxm : x ∈ m.segments),
            ¬ ∃ σw ∈ (MW.leadingChain m).val.segments, ∃ hσwm : σw ∈ m.segments,
              x.a = σw.a ∧ x.b < σw.b ∧
              depth_of_segment m x hxm = depth_of_segment m σw hσwm := by
          rintro hxm ⟨σw, hσwC, hσwm, hwa, hwb, -⟩
          have := begin_unique_of_pairwise_lt _ hBlt σw hσwC σ hσC (by omega)
          have hb := congrArg Segment.b this
          simp only [] at hb
          omega
        by_cases hf : ∃ hxm : x ∈ m.segments,
            depth_of_segment m x hxm = depth_of_segment m σ hσm
        · obtain ⟨hxm, hxd⟩ := hf
          have hBm : ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count x
              = m.segments.count x :=
            bucket_count_eq_of_depth m _ x (fun hxm2 => by
              have : depth_of_segment m x hxm2 = depth_of_segment m x hxm := rfl
              omega)
          have hx' : x ∈ (MW.makeResidual m (MW.leadingChain m).val.segments).segments :=
            survivor_mem_mdag m _ x hxm hxnotC
          have hB : ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
              (depth_of_segment m σ hσm)).map (·.val)).count x
              = (MW.makeResidual m (MW.leadingChain m).val.segments).segments.count x := by
            apply bucket_count_eq_of_depth
            intro hx'2
            rw [mdag_depth_survivor m sₘ s_l hsₘ hs_l hmin x hxm hx'2 (hcert hxm)]
            exact hxd
          rw [hB, hBm, if_neg (fun h => by
              have := congrArg Segment.b h; simp only [] at this; omega),
            if_neg (by rintro ⟨-, h⟩; omega), if_neg (by rintro ⟨h, -⟩; omega)]
          omega
        · have hBm : ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count x = 0 :=
            bucket_count_eq_zero_of_depth_ne m _ x (fun hxm h => hf ⟨hxm, h⟩)
          have hB : ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
              (depth_of_segment m σ hσm)).map (·.val)).count x = 0 := by
            apply bucket_count_eq_zero_of_depth_ne
            intro hx'
            rcases mem_mdag_cases m _ x hx' with hxm | ⟨c, hcC, hcnd, hxa, hxb⟩
            · rw [mdag_depth_survivor m sₘ s_l hsₘ hs_l hmin x hxm hx' (hcert hxm)]
              exact fun h => hf ⟨hxm, h⟩
            · exact absurd ⟨c, hcC, hcnd, hxa, hxb⟩ hst
          rw [hB, hBm, if_neg (fun h => by
              have := congrArg Segment.b h; simp only [] at this; omega),
            if_neg (by rintro ⟨-, h⟩; omega), if_neg (by rintro ⟨h, -⟩; omega)]
  · by_cases hx5 : x.a = σ.a + 1
    · -- begin one past the last chain element
      have hxnotC : x ∉ (MW.leadingChain m).val.segments := by
        intro hx
        have := hmaxa x hx
        omega
      by_cases hx6 : x.b = σ.b
      · -- the starred value ⁻σ
        rw [if_neg hxnotC, if_pos ⟨σ, hσC, hnd, by omega, by omega⟩] at hcount
        have hx' : x ∈ (MW.makeResidual m (MW.leadingChain m).val.segments).segments := by
          rw [← List.count_pos_iff]
          omega
        have hB : ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
            (depth_of_segment m σ hσm)).map (·.val)).count x
            = (MW.makeResidual m (MW.leadingChain m).val.segments).segments.count x := by
          apply bucket_count_eq_of_depth
          intro hx'2
          exact mdag_depth_starred' m sₘ s_l hsₘ hs_l hmin σ hσC hσm hnd x
            (by omega) (by omega) hx'2
        have hBm : ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count x
            = m.segments.count x := by
          apply bucket_count_eq_of_depth
          intro hxm
          have hge := depth_mdag_ge_notC m sₘ s_l hsₘ hs_l hmin x hxm hxnotC hx'
          have hub := (mdag_depth_bound m sₘ s_l hsₘ hs_l hmin _).1 x hxm hx' rfl
          have hdd := mdag_depth_starred' m sₘ s_l hsₘ hs_l hmin σ hσC hσm hnd x
            (by omega) (by omega) hx'
          rcases Nat.lt_or_ge (depth_of_segment m x hxm)
            (depth_of_segment m σ hσm) with hlt | hge2
          · exfalso
            obtain ⟨σw, hσwC, -, hwa, -, -⟩ := hub.2 (by omega)
            have := hmaxa σw hσwC
            omega
          · omega
        rw [hB, hBm, if_neg (fun h => by
            have := congrArg Segment.a h; simp only [] at this; omega),
          if_neg (by rintro ⟨h, -⟩; omega), if_pos ⟨hx5, hx6⟩]
        omega
      · -- other values one past σ: nothing changes
        have hst : ¬ ∃ c ∈ (MW.leadingChain m).val.segments,
            c.a < c.b ∧ x.a = c.a + 1 ∧ x.b = c.b := by
          rintro ⟨c, hcC, -, hca, hcb⟩
          have := begin_unique_of_pairwise_lt _ hBlt c hcC σ hσC (by omega)
          rw [this] at hcb
          omega
        rw [if_neg hxnotC, if_neg hst] at hcount
        have hcert : ∀ (hxm : x ∈ m.segments),
            ¬ ∃ σw ∈ (MW.leadingChain m).val.segments, ∃ hσwm : σw ∈ m.segments,
              x.a = σw.a ∧ x.b < σw.b ∧
              depth_of_segment m x hxm = depth_of_segment m σw hσwm := by
          rintro hxm ⟨σw, hσwC, hσwm, hwa, hwb, -⟩
          have := hmaxa σw hσwC
          omega
        by_cases hf : ∃ hxm : x ∈ m.segments,
            depth_of_segment m x hxm = depth_of_segment m σ hσm
        · obtain ⟨hxm, hxd⟩ := hf
          have hBm : ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count x
              = m.segments.count x :=
            bucket_count_eq_of_depth m _ x (fun hxm2 => by
              have : depth_of_segment m x hxm2 = depth_of_segment m x hxm := rfl
              omega)
          have hx' : x ∈ (MW.makeResidual m (MW.leadingChain m).val.segments).segments :=
            survivor_mem_mdag m _ x hxm hxnotC
          have hB : ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
              (depth_of_segment m σ hσm)).map (·.val)).count x
              = (MW.makeResidual m (MW.leadingChain m).val.segments).segments.count x := by
            apply bucket_count_eq_of_depth
            intro hx'2
            rw [mdag_depth_survivor m sₘ s_l hsₘ hs_l hmin x hxm hx'2 (hcert hxm)]
            exact hxd
          rw [hB, hBm, if_neg (fun h => by
              have := congrArg Segment.a h; simp only [] at this; omega),
            if_neg (by rintro ⟨h, -⟩; omega), if_neg (by rintro ⟨-, h⟩; omega)]
          omega
        · have hBm : ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count x = 0 :=
            bucket_count_eq_zero_of_depth_ne m _ x (fun hxm h => hf ⟨hxm, h⟩)
          have hB : ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
              (depth_of_segment m σ hσm)).map (·.val)).count x = 0 := by
            apply bucket_count_eq_zero_of_depth_ne
            intro hx'
            rcases mem_mdag_cases m _ x hx' with hxm | ⟨c, hcC, hcnd, hxa, hxb⟩
            · rw [mdag_depth_survivor m sₘ s_l hsₘ hs_l hmin x hxm hx' (hcert hxm)]
              exact fun h => hf ⟨hxm, h⟩
            · exact absurd ⟨c, hcC, hcnd, hxa, hxb⟩ hst
          rw [hB, hBm, if_neg (fun h => by
              have := congrArg Segment.a h; simp only [] at this; omega),
            if_neg (by rintro ⟨h, -⟩; omega), if_neg (by rintro ⟨-, h⟩; omega)]
    · -- begins outside both groups
      rw [if_neg (fun h => by
          have := congrArg Segment.a h; simp only [] at this; omega),
        if_neg (by rintro ⟨h, -⟩; omega), if_neg (by rintro ⟨h, -⟩; omega)]
      have hgoal : ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
          (depth_of_segment m σ hσm)).map (·.val)).count x
          = ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count x := by
        by_cases hxC : x ∈ (MW.leadingChain m).val.segments
        · have hxm := hCsub x hxC
          have hend : depth_of_segment m x hxm ≠ depth_of_segment m σ hσm :=
            chain_mem_depth_ne m x σ hxC hσC hx1 hxm hσm
          rw [bucket_count_eq_zero_of_depth_ne m _ x (fun hxm2 h => by
            have : depth_of_segment m x hxm2 = depth_of_segment m x hxm := rfl
            omega)]
          apply bucket_count_eq_zero_of_depth_ne
          intro hx'
          rw [mdag_depth_survivor m sₘ s_l hsₘ hs_l hmin x hxm hx' ?_]
          · exact hend
          · rintro ⟨σw, hσwC, hσwm, hwa, hwb, -⟩
            have := begin_unique_of_pairwise_lt _ hBlt σw hσwC x hxC (by omega)
            rw [this] at hwb
            omega
        · by_cases hstt : ∃ c ∈ (MW.leadingChain m).val.segments,
              c.a < c.b ∧ x.a = c.a + 1 ∧ x.b = c.b
          · obtain ⟨c, hcC, hcnd, hxa, hxb⟩ := hstt
            have hcm := hCsub c hcC
            have hdc : depth_of_segment m c hcm ≠ depth_of_segment m σ hσm :=
              chain_mem_depth_ne m c σ hcC hσC (by omega) hcm hσm
            have hx' : x ∈ (MW.makeResidual m
                (MW.leadingChain m).val.segments).segments := by
              rw [← List.count_pos_iff]
              rw [if_neg hxC, if_pos ⟨c, hcC, hcnd, hxa, hxb⟩] at hcount
              omega
            have hdd := mdag_depth_starred' m sₘ s_l hsₘ hs_l hmin c hcC hcm hcnd
              x hxa hxb hx'
            have hB : ((bucket (MW.makeResidual m
                (MW.leadingChain m).val.segments)
                (depth_of_segment m σ hσm)).map (·.val)).count x = 0 := by
              apply bucket_count_eq_zero_of_depth_ne
              intro hx'2
              have hpi : depth_of_segment (MW.makeResidual m
                  (MW.leadingChain m).val.segments) x hx'2
                  = depth_of_segment (MW.makeResidual m
                  (MW.leadingChain m).val.segments) x hx' := rfl
              omega
            rw [hB]
            symm
            apply bucket_count_eq_zero_of_depth_ne
            intro hxm hxd
            have hge := depth_mdag_ge_notC m sₘ s_l hsₘ hs_l hmin x hxm hxC hx'
            have hub := (mdag_depth_bound m sₘ s_l hsₘ hs_l hmin _).1 x hxm hx' rfl
            obtain ⟨σw, hσwC, hσwm, hwa, hwb, hwd⟩ := hub.2 (by omega)
            have hwne : σw.a ≠ σ.a := by omega
            have := chain_mem_depth_ne m σw σ hσwC hσC hwne hσwm hσm
            omega
          · rw [if_neg hxC, if_neg hstt] at hcount
            by_cases hxm : x ∈ m.segments
            · by_cases hsp : ∃ σw ∈ (MW.leadingChain m).val.segments,
                  ∃ hσwm : σw ∈ m.segments, x.a = σw.a ∧ x.b < σw.b ∧
                  depth_of_segment m x hxm = depth_of_segment m σw hσwm
              · obtain ⟨σw, hσwC, hσwm, hwa, hwb, hwd⟩ := hsp
                have hwne : σw.a ≠ σ.a := by omega
                have hdw : depth_of_segment m σw hσwm ≠ depth_of_segment m σ hσm :=
                  chain_mem_depth_ne m σw σ hσwC hσC hwne hσwm hσm
                have hB1 : ((bucket m
                    (depth_of_segment m σ hσm)).map (·.val)).count x = 0 :=
                  bucket_count_eq_zero_of_depth_ne m _ x (fun hxm2 h => by
                    have : depth_of_segment m x hxm2 = depth_of_segment m x hxm := rfl
                    omega)
                rw [hB1]
                apply bucket_count_eq_zero_of_depth_ne
                intro hx'
                have hdep := special_moves_up m sₘ s_l hsₘ hs_l hmin x hxm hx'
                  σw hσwC hσwm hwa hwb hwd
                intro hcon
                have hheadne : (MW.leadingChain m).val.segments.head? ≠ some σw := by
                  rw [MW.leadingChain_head m sₘ hsₘ]
                  intro h
                  have heq := Option.some.inj h
                  have ha := congrArg Segment.a heq
                  have hb := congrArg Segment.b heq
                  simp only [] at ha hb
                  exact no_special_head m sₘ hsₘ x hxm (by omega) (by omega)
                obtain ⟨u₂, σp, v₂, hsplit₂⟩ :=
                  exists_pred_split (MW.leadingChain m).val.segments σw hσwC hheadne
                have hσpC : σp ∈ (MW.leadingChain m).val.segments := by
                  rw [hsplit₂]; simp
                have hσpm := hCsub σp hσpC
                have hgap := special_witness_gap m sₘ s_l hsₘ hs_l hmin x hxm
                  σw hσwm hwa hwb hwd u₂ v₂ σp hsplit₂ hσpm
                have hpσ : σp = σ := by
                  by_contra hne
                  have hpa : σp.a ≠ σ.a := by
                    intro ha
                    exact hne (begin_unique_of_pairwise_lt _ hBlt σp hσpC σ hσC ha)
                  have := chain_mem_depth_ne m σp σ hσpC hσC hpa hσpm hσm
                  omega
                subst hpσ
                obtain ⟨-, hv⟩ := split_unique_of_pairwise_lt _ hBlt
                  u₂ (σw :: v₂) u [] σp hsplit₂ hsplit
                simp at hv
              · have hx' : x ∈ (MW.makeResidual m
                    (MW.leadingChain m).val.segments).segments :=
                  survivor_mem_mdag m _ x hxm hxC
                have hdep := mdag_depth_survivor m sₘ s_l hsₘ hs_l hmin x hxm hx' hsp
                by_cases hf : depth_of_segment m x hxm = depth_of_segment m σ hσm
                · rw [bucket_count_eq_of_depth m _ x (fun hxm2 => by
                    have : depth_of_segment m x hxm2 = depth_of_segment m x hxm := rfl
                    omega)]
                  rw [bucket_count_eq_of_depth _ _ x (fun hx'2 => by
                    have hpi : depth_of_segment (MW.makeResidual m
                        (MW.leadingChain m).val.segments) x hx'2
                        = depth_of_segment (MW.makeResidual m
                        (MW.leadingChain m).val.segments) x hx' := rfl
                    omega)]
                  omega
                · rw [bucket_count_eq_zero_of_depth_ne m _ x (fun hxm2 h => by
                    have : depth_of_segment m x hxm2 = depth_of_segment m x hxm := rfl
                    omega)]
                  apply bucket_count_eq_zero_of_depth_ne
                  intro hx'2
                  have hpi : depth_of_segment (MW.makeResidual m
                      (MW.leadingChain m).val.segments) x hx'2
                      = depth_of_segment (MW.makeResidual m
                      (MW.leadingChain m).val.segments) x hx' := rfl
                  omega
            · have hB : ((bucket (MW.makeResidual m
                  (MW.leadingChain m).val.segments)
                  (depth_of_segment m σ hσm)).map (·.val)).count x = 0 := by
                apply bucket_count_eq_zero_of_depth_ne
                intro hx'
                have := List.count_pos_iff.mpr hx'
                have hzero : m.segments.count x = 0 := List.count_eq_zero.mpr hxm
                omega
              rw [hB, bucket_count_eq_zero_of_depth_ne m _ x (fun hxm2 _ => hxm hxm2)]
      omega

/-! ## Indicator evaluation helpers -/

/-- Every nonempty begin-group has a maximal end. -/
lemma exists_group_top : ∀ (L : List Segment) (a : ℤ), (∃ y ∈ L, y.a = a) →
    ∃ E, (∃ y ∈ L, y.a = a ∧ y.b = E) ∧ ∀ z ∈ L, z.a = a → z.b ≤ E := by
  intro L
  induction L with
  | nil => rintro a ⟨y, hy, -⟩; simp at hy
  | cons c cs ih =>
    rintro a ⟨y, hy, hya⟩
    by_cases hgrp : ∃ y ∈ cs, y.a = a
    · obtain ⟨E, ⟨z, hz, hza, hzb⟩, hmax⟩ := ih a hgrp
      by_cases hca : c.a = a
      · refine ⟨max c.b E, ?_, ?_⟩
        · rcases le_total c.b E with h | h
          · exact ⟨z, List.mem_cons_of_mem _ hz, hza, by omega⟩
          · exact ⟨c, List.mem_cons_self, hca, by omega⟩
        · intro w hw hwa
          rcases List.mem_cons.mp hw with rfl | hwr
          · omega
          · have := hmax w hwr hwa; omega
      · refine ⟨E, ⟨z, List.mem_cons_of_mem _ hz, hza, hzb⟩, ?_⟩
        intro w hw hwa
        rcases List.mem_cons.mp hw with rfl | hwr
        · exact absurd hwa hca
        · exact hmax w hwr hwa
    · -- the group is exactly the head
      have hyc : y = c := by
        rcases List.mem_cons.mp hy with rfl | hyr
        · rfl
        · exact absurd ⟨y, hyr, hya⟩ hgrp
      subst hyc
      refine ⟨y.b, ⟨y, List.mem_cons_self, hya, rfl⟩, ?_⟩
      intro w hw hwa
      rcases List.mem_cons.mp hw with rfl | hwr
      · exact le_refl _
      · exact absurd ⟨w, hwr, hwa⟩ hgrp

/-- Every nonempty above-region has a first begin-group, with its maximal end. -/
lemma exists_next_data : ∀ (L : List Segment) (a : ℤ), (∃ y ∈ L, a < y.a) →
    ∃ a' E', a < a' ∧ (∃ z ∈ L, z.a = a' ∧ z.b = E') ∧
      (∀ y ∈ L, a < y.a → a' ≤ y.a) ∧ (∀ z ∈ L, z.a = a' → z.b ≤ E') := by
  intro L
  induction L with
  | nil => rintro a ⟨y, hy, -⟩; simp at hy
  | cons c cs ih =>
    rintro a ⟨y, hy, hya⟩
    by_cases habove : ∃ y ∈ cs, a < y.a
    · obtain ⟨a', E', ha', ⟨z, hz, hza, hzb⟩, hmin, hmax⟩ := ih a habove
      by_cases hca : a < c.a
      · rcases lt_trichotomy c.a a' with hlt | heq | hgt
        · -- c starts a new, earlier group
          refine ⟨c.a, c.b, hca, ⟨c, List.mem_cons_self, rfl, rfl⟩, ?_, ?_⟩
          · intro w hw hwa
            rcases List.mem_cons.mp hw with rfl | hwr
            · exact le_refl _
            · have := hmin w hwr hwa; omega
          · intro w hw hwa
            rcases List.mem_cons.mp hw with rfl | hwr
            · exact le_refl _
            · have := hmin w hwr (by omega); omega
        · -- c joins the first group
          refine ⟨a', max c.b E', ha', ?_, ?_, ?_⟩
          · rcases le_total c.b E' with h | h
            · exact ⟨z, List.mem_cons_of_mem _ hz, hza, by omega⟩
            · exact ⟨c, List.mem_cons_self, heq, by omega⟩
          · intro w hw hwa
            rcases List.mem_cons.mp hw with rfl | hwr
            · omega
            · exact hmin w hwr hwa
          · intro w hw hwa
            rcases List.mem_cons.mp hw with rfl | hwr
            · omega
            · have := hmax w hwr hwa; omega
        · -- c comes later
          refine ⟨a', E', ha', ⟨z, List.mem_cons_of_mem _ hz, hza, hzb⟩, ?_, ?_⟩
          · intro w hw hwa
            rcases List.mem_cons.mp hw with rfl | hwr
            · omega
            · exact hmin w hwr hwa
          · intro w hw hwa
            rcases List.mem_cons.mp hw with rfl | hwr
            · omega
            · exact hmax w hwr hwa
      · refine ⟨a', E', ha', ⟨z, List.mem_cons_of_mem _ hz, hza, hzb⟩, ?_, ?_⟩
        · intro w hw hwa
          rcases List.mem_cons.mp hw with rfl | hwr
          · exact absurd hwa hca
          · exact hmin w hwr hwa
        · intro w hw hwa
          rcases List.mem_cons.mp hw with rfl | hwr
          · exfalso; exact hca (by omega)
          · exact hmax w hwr hwa
    · -- the above-region is exactly the head
      have hyc : y = c := by
        rcases List.mem_cons.mp hy with rfl | hyr
        · rfl
        · exact absurd ⟨y, hyr, hya⟩ habove
      subst hyc
      refine ⟨y.a, y.b, hya, ⟨y, List.mem_cons_self, rfl, rfl⟩, ?_, ?_⟩
      · intro w hw hwa
        rcases List.mem_cons.mp hw with rfl | hwr
        · exact le_refl _
        · exact absurd ⟨w, hwr, hwa⟩ habove
      · intro w hw hwa
        rcases List.mem_cons.mp hw with rfl | hwr
        · exact le_refl _
        · exact absurd ⟨w, hwr, by omega⟩ habove

/-- `topInd` through a known group top. -/
lemma topInd_eq_group (L : List Segment) (w : ℤ × ℤ) (E : ℤ)
    (hE1 : ∃ y ∈ L, y.a = w.1 ∧ y.b = E) (hE2 : ∀ z ∈ L, z.a = w.1 → z.b ≤ E) :
    topInd L w = if w.2 = E then 1 else 0 := by
  unfold topInd
  obtain ⟨y, hy, hya, hyb⟩ := hE1
  by_cases hw2 : w.2 = E
  · rw [if_pos ⟨y, hy, hya, by omega, fun z hz hza => by
      have := hE2 z hz hza; omega⟩, if_pos hw2]
  · rw [if_neg, if_neg hw2]
    rintro ⟨x', hx', ha', hb', hmax'⟩
    have h1 := hE2 x' hx' ha'
    have h2 := hmax' y hy hya
    omega

/-- `transInd` through known next-group data. -/
lemma transInd_eq_group (L : List Segment) (w : ℤ × ℤ)
    (hsrc : ∃ x ∈ L, x.a = w.1) (a' E' : ℤ) (ha' : w.1 < a')
    (hwit : ∃ z ∈ L, z.a = a' ∧ z.b = E')
    (hmin : ∀ y ∈ L, w.1 < y.a → a' ≤ y.a)
    (hmax : ∀ z ∈ L, z.a = a' → z.b ≤ E') :
    transInd L w = if w.2 = E' then 1 else 0 := by
  unfold transInd
  obtain ⟨x, hx, hxa⟩ := hsrc
  obtain ⟨z, hz, hza, hzb⟩ := hwit
  by_cases hw2 : w.2 = E'
  · rw [if_pos ⟨x, hx, hxa, z, hz, by omega, by omega,
      fun y hy hya => by have := hmin y hy (by omega); omega,
      fun y hy hya => by have := hmax y hy (by omega); omega⟩, if_pos hw2]
  · rw [if_neg, if_neg hw2]
    rintro ⟨x', hx', ha'', z', hz', hlt', hzb', hmin', hmax'⟩
    -- the target group is forced: z'.a = a' and z'.b = E'
    have h1 : a' ≤ z'.a := hmin z' hz' (by omega)
    have h2 : z'.a ≤ z.a := hmin' z hz (by omega)
    have h3 : z'.a = a' := by omega
    have h4 := hmax z' hz' h3
    have h5 := hmax' z hz (by omega)
    omega

/-- `transInd` vanishes when nothing lies above the source begin. -/
lemma transInd_eq_zero_of_no_next (L : List Segment) (w : ℤ × ℤ)
    (h : ∀ y ∈ L, ¬ w.1 < y.a) : transInd L w = 0 := by
  unfold transInd
  rw [if_neg]
  rintro ⟨x', hx', ha', z, hz, hlt, -⟩
  exact h z hz (by omega)

/-- Pair equality componentwise. -/
lemma pair_eq_iff (w : ℤ × ℤ) (p q : ℤ) : w = (p, q) ↔ (w.1 = p ∧ w.2 = q) := by
  constructor
  · intro h; rw [h]; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    have hw : w = (w.1, w.2) := rfl
    rw [hw, h1, h2]

/-- **Indicator transport at a chain fiber**: the tops-and-transitions corrections
between a fiber `Fm` of `m` and its `m†` counterpart `Fd`. `σ` is the chain value, `t`
its boundary partner; the set-level hypotheses record how the two fibers differ. -/
lemma indicator_transport (Fm Fd : List Segment) (σ t : Segment)
    (hσmem : σ ∈ Fm) (hta : σ.a < t.a) (htmem : t ∈ Fm)
    (hnextt : ∀ y ∈ Fm, σ.a < y.a → t.a ≤ y.a ∧ y.b ≤ t.b)
    (hA1 : ∀ y ∈ Fd, y.a = σ.a → y ∈ Fm ∧ σ.b ≤ y.b)
    (hA2 : ∀ y ∈ Fm, y.a = σ.a → σ.b < y.b → y ∈ Fd)
    (hB1 : ∃ y ∈ Fd, y.a = σ.a + 1 ∧ y.b = σ.b)
    (hB2 : ∀ y ∈ Fd, y.a = σ.a + 1 → y.b ≤ σ.b)
    (hD1 : ∀ y : Segment, y.a ≠ σ.a → y.a ≠ σ.a + 1 → (y ∈ Fd ↔ y ∈ Fm))
    (w : ℤ × ℤ) :
    transInd Fd w + (if w = ((σ.a : ℤ), (t.b : ℤ)) then 1 else 0)
      + (if w = ((σ.a + 1 : ℤ), (σ.b : ℤ)) then 1 else 0) + topInd Fm w
    = transInd Fm w + (if w = ((σ.a + 1 : ℤ), (t.b : ℤ)) then 1 else 0)
      + (if w = ((σ.a : ℤ), (σ.b : ℤ)) then 1 else 0) + topInd Fd w := by
  classical
  obtain ⟨E, hEwit, hEmax⟩ := exists_group_top Fm σ.a ⟨σ, hσmem, rfl⟩
  have hEσ : σ.b ≤ E := hEmax σ hσmem rfl
  obtain ⟨yB, hyB, hyBa, hyBb⟩ := hB1
  by_cases hw1 : w.1 = σ.a
  · -- source begin σ.a
    have htm : topInd Fm w = if w.2 = E then 1 else 0 := by
      apply topInd_eq_group Fm w E ?_ ?_
      · obtain ⟨y, hy, hya, hyb⟩ := hEwit
        exact ⟨y, hy, by omega, hyb⟩
      · intro z hz hza
        exact hEmax z hz (by omega)
    have htrm : transInd Fm w = if w.2 = t.b then 1 else 0 := by
      apply transInd_eq_group Fm w ⟨σ, hσmem, hw1.symm⟩ t.a t.b (by omega)
        ⟨t, htmem, rfl, rfl⟩
      · intro y hy hya
        exact (hnextt y hy (by omega)).1
      · intro z hz hza
        exact (hnextt z hz (by omega)).2
    by_cases hsurv : ∃ y ∈ Fd, y.a = σ.a
    · obtain ⟨y₀, hy₀, hy₀a⟩ := hsurv
      have htrd : transInd Fd w = if w.2 = σ.b then 1 else 0 := by
        apply transInd_eq_group Fd w ⟨y₀, hy₀, by omega⟩ (σ.a + 1) σ.b (by omega)
          ⟨yB, hyB, hyBa, hyBb⟩
        · intro y hy hya
          omega
        · exact hB2
      have htd : topInd Fd w = if w.2 = E then 1 else 0 := by
        apply topInd_eq_group Fd w E ?_ ?_
        · rcases eq_or_lt_of_le hEσ with heq | hlt
          · -- E = σ.b: any survivor attains it
            obtain ⟨hy₀m, hy₀b⟩ := hA1 y₀ hy₀ hy₀a
            have := hEmax y₀ hy₀m hy₀a
            exact ⟨y₀, hy₀, by omega, by omega⟩
          · -- E > σ.b: the old top survives
            obtain ⟨yE, hyE, hyEa, hyEb⟩ := hEwit
            exact ⟨yE, hA2 yE hyE hyEa (by omega), by omega, hyEb⟩
        · intro z hz hza
          obtain ⟨hzm, -⟩ := hA1 z hz (by omega)
          exact hEmax z hzm (by omega)
      rw [htm, htrm, htrd, htd]
      simp only [pair_eq_iff]
      split_ifs <;> omega
    · have htrd : transInd Fd w = 0 :=
        transInd_eq_zero Fd w (fun x hx hxa => hsurv ⟨x, hx, by omega⟩)
      have htd : topInd Fd w = 0 :=
        topInd_eq_zero Fd w (fun x hx hxa => hsurv ⟨x, hx, by omega⟩)
      have hEeq : E = σ.b := by
        rcases eq_or_lt_of_le hEσ with heq | hlt
        · omega
        · exfalso
          obtain ⟨yE, hyE, hyEa, hyEb⟩ := hEwit
          exact hsurv ⟨yE, hA2 yE hyE hyEa (by omega), hyEa⟩
      rw [htm, htrm, htrd, htd, hEeq]
      simp only [pair_eq_iff]
      split_ifs <;> omega
  · by_cases hw1' : w.1 = σ.a + 1
    · -- source begin σ.a + 1
      have htd : topInd Fd w = if w.2 = σ.b then 1 else 0 := by
        apply topInd_eq_group Fd w σ.b ⟨yB, hyB, by omega, hyBb⟩
        intro z hz hza
        exact hB2 z hz (by omega)
      by_cases hY : ∃ y ∈ Fm, y.a = σ.a + 1
      · obtain ⟨y₀, hy₀, hy₀a⟩ := hY
        have hta' : t.a = σ.a + 1 := by
          have := (hnextt y₀ hy₀ (by omega)).1
          omega
        have htm : topInd Fm w = if w.2 = t.b then 1 else 0 := by
          apply topInd_eq_group Fm w t.b ⟨t, htmem, by omega, rfl⟩
          intro z hz hza
          exact (hnextt z hz (by omega)).2
        by_cases hZ : ∃ y ∈ Fm, σ.a + 1 < y.a
        · obtain ⟨a₂, E₂, ha₂, ⟨z₂, hz₂, hz₂a, hz₂b⟩, hmin₂, hmax₂⟩ :=
            exists_next_data Fm (σ.a + 1) hZ
          have hz₂d : z₂ ∈ Fd := (hD1 z₂ (by omega) (by omega)).mpr hz₂
          have htrm : transInd Fm w = if w.2 = E₂ then 1 else 0 := by
            apply transInd_eq_group Fm w ⟨y₀, hy₀, by omega⟩ a₂ E₂ (by omega)
              ⟨z₂, hz₂, hz₂a, hz₂b⟩
            · intro y hy hya
              exact hmin₂ y hy (by omega)
            · exact hmax₂
          have htrd : transInd Fd w = if w.2 = E₂ then 1 else 0 := by
            apply transInd_eq_group Fd w ⟨yB, hyB, by omega⟩ a₂ E₂ (by omega)
              ⟨z₂, hz₂d, hz₂a, hz₂b⟩
            · intro y hy hya
              have hym : y ∈ Fm := (hD1 y (by omega) (by omega)).mp hy
              exact hmin₂ y hym (by omega)
            · intro z hz hza
              have hzm : z ∈ Fm := (hD1 z (by omega) (by omega)).mp hz
              exact hmax₂ z hzm hza
          rw [htm, htd, htrm, htrd]
          simp only [pair_eq_iff]
          split_ifs <;> omega
        · have htrm : transInd Fm w = 0 :=
            transInd_eq_zero_of_no_next Fm w (fun y hy h => hZ ⟨y, hy, by omega⟩)
          have htrd : transInd Fd w = 0 := by
            apply transInd_eq_zero_of_no_next Fd w
            intro y hy h
            have hym : y ∈ Fm := (hD1 y (by omega) (by omega)).mp hy
            exact hZ ⟨y, hym, by omega⟩
          rw [htm, htd, htrm, htrd]
          simp only [pair_eq_iff]
          split_ifs <;> omega
      · -- old fiber has nothing at σ.a + 1
        have htm : topInd Fm w = 0 :=
          topInd_eq_zero Fm w (fun x hx hxa => hY ⟨x, hx, by omega⟩)
        have htrm : transInd Fm w = 0 :=
          transInd_eq_zero Fm w (fun x hx hxa => hY ⟨x, hx, by omega⟩)
        have htZ : σ.a + 1 < t.a := by
          rcases eq_or_lt_of_le (by omega : σ.a + 1 ≤ t.a) with heq | hlt
          · exact absurd ⟨t, htmem, heq.symm⟩ hY
          · exact hlt
        have htrd : transInd Fd w = if w.2 = t.b then 1 else 0 := by
          apply transInd_eq_group Fd w ⟨yB, hyB, by omega⟩ t.a t.b (by omega)
            ⟨t, (hD1 t (by omega) (by omega)).mpr htmem, rfl, rfl⟩
          · intro y hy hya
            have hym : y ∈ Fm := (hD1 y (by omega) (by omega)).mp hy
            exact (hnextt y hym (by omega)).1
          · intro z hz hza
            have hzm : z ∈ Fm := (hD1 z (by omega) (by omega)).mp hz
            exact (hnextt z hzm (by omega)).2
        rw [htm, htd, htrm, htrd]
        simp only [pair_eq_iff]
        split_ifs <;> omega
    · -- begins outside both groups: everything transports
      have htop : topInd Fd w = topInd Fm w := by
        by_cases hgrp : ∃ y ∈ Fm, y.a = w.1
        · obtain ⟨Ew, hEwwit, hEwmax⟩ := exists_group_top Fm w.1 hgrp
          obtain ⟨yw, hyw, hywa, hywb⟩ := hEwwit
          have hywd : yw ∈ Fd := (hD1 yw (by omega) (by omega)).mpr hyw
          rw [topInd_eq_group Fm w Ew ⟨yw, hyw, hywa, hywb⟩ hEwmax,
            topInd_eq_group Fd w Ew ⟨yw, hywd, hywa, hywb⟩ ?_]
          intro z hz hza
          have hzm : z ∈ Fm := (hD1 z (by omega) (by omega)).mp hz
          exact hEwmax z hzm hza
        · rw [topInd_eq_zero Fm w (fun x hx hxa => hgrp ⟨x, hx, hxa⟩),
            topInd_eq_zero Fd w (fun x hx hxa => hgrp
              ⟨x, (hD1 x (by omega) (by omega)).mp hx, hxa⟩)]
      have htrans : transInd Fd w = transInd Fm w := by
        by_cases hsrc : ∃ x ∈ Fm, x.a = w.1
        · obtain ⟨xs, hxs, hxsa⟩ := hsrc
          have hxsd : xs ∈ Fd := (hD1 xs (by omega) (by omega)).mpr hxs
          by_cases hab : ∃ y ∈ Fm, w.1 < y.a
          · obtain ⟨a₂, E₂, ha₂, ⟨z₂, hz₂, hz₂a, hz₂b⟩, hmin₂, hmax₂⟩ :=
              exists_next_data Fm w.1 hab
            rcases lt_trichotomy a₂ σ.a with hlt | heq | hgt
            · -- next group strictly before σ: pure transfer
              have hz₂d : z₂ ∈ Fd := (hD1 z₂ (by omega) (by omega)).mpr hz₂
              rw [transInd_eq_group Fm w ⟨xs, hxs, hxsa⟩ a₂ E₂ ha₂
                  ⟨z₂, hz₂, hz₂a, hz₂b⟩ hmin₂ hmax₂,
                transInd_eq_group Fd w ⟨xs, hxsd, hxsa⟩ a₂ E₂ ha₂
                  ⟨z₂, hz₂d, hz₂a, hz₂b⟩ ?_ ?_]
              · intro y hy hya
                by_cases hyσ : y.a = σ.a
                · omega
                · by_cases hyσ' : y.a = σ.a + 1
                  · omega
                  · exact hmin₂ y ((hD1 y hyσ hyσ').mp hy) hya
              · intro z hz hza
                exact hmax₂ z ((hD1 z (by omega) (by omega)).mp hz) hza
            · -- next group is σ's
              have hE₂E : E₂ = E := by
                obtain ⟨yE, hyE, hyEa, hyEb⟩ := hEwit
                have h1 := hEmax z₂ hz₂ (by omega)
                have h2 := hmax₂ yE hyE (by omega)
                omega
              have hwlt : w.1 < σ.a := by omega
              rw [transInd_eq_group Fm w ⟨xs, hxs, hxsa⟩ a₂ E₂ ha₂
                  ⟨z₂, hz₂, hz₂a, hz₂b⟩ hmin₂ hmax₂]
              by_cases hsurv : ∃ y ∈ Fd, y.a = σ.a
              · obtain ⟨y₀, hy₀, hy₀a⟩ := hsurv
                rw [transInd_eq_group Fd w ⟨xs, hxsd, hxsa⟩ σ.a E (by omega) ?_ ?_ ?_]
                · rw [hE₂E]
                · rcases eq_or_lt_of_le hEσ with heq2 | hlt2
                  · obtain ⟨hy₀m, hy₀b⟩ := hA1 y₀ hy₀ hy₀a
                    have := hEmax y₀ hy₀m hy₀a
                    exact ⟨y₀, hy₀, by omega, by omega⟩
                  · obtain ⟨yE, hyE, hyEa, hyEb⟩ := hEwit
                    exact ⟨yE, hA2 yE hyE hyEa (by omega), by omega, hyEb⟩
                · intro y hy hya
                  by_cases hyσ : y.a = σ.a
                  · omega
                  · by_cases hyσ' : y.a = σ.a + 1
                    · omega
                    · have := hmin₂ y ((hD1 y hyσ hyσ').mp hy) hya
                      omega
                · intro z hz hza
                  obtain ⟨hzm, -⟩ := hA1 z hz hza
                  exact hEmax z hzm hza
              · have hEeq : E = σ.b := by
                  rcases eq_or_lt_of_le hEσ with heq2 | hlt2
                  · omega
                  · exfalso
                    obtain ⟨yE, hyE, hyEa, hyEb⟩ := hEwit
                    exact hsurv ⟨yE, hA2 yE hyE hyEa (by omega), hyEa⟩
                rw [transInd_eq_group Fd w ⟨xs, hxsd, hxsa⟩ (σ.a + 1) σ.b (by omega)
                    ⟨yB, hyB, hyBa, hyBb⟩ ?_ hB2]
                · rw [hE₂E, hEeq]
                · intro y hy hya
                  by_cases hyσ : y.a = σ.a
                  · exact absurd ⟨y, hy, hyσ⟩ hsurv
                  · by_cases hyσ' : y.a = σ.a + 1
                    · omega
                    · have := hmin₂ y ((hD1 y hyσ hyσ').mp hy) hya
                      omega
            · -- everything above w.1 is beyond σ + 1: pure transfer
              have hwgt : σ.a + 1 < w.1 := by
                have := hmin₂ σ hσmem
                by_cases h : w.1 < σ.a
                · exfalso; have := this h; omega
                · omega
              have hz₂d : z₂ ∈ Fd := (hD1 z₂ (by omega) (by omega)).mpr hz₂
              rw [transInd_eq_group Fm w ⟨xs, hxs, hxsa⟩ a₂ E₂ ha₂
                  ⟨z₂, hz₂, hz₂a, hz₂b⟩ hmin₂ hmax₂,
                transInd_eq_group Fd w ⟨xs, hxsd, hxsa⟩ a₂ E₂ ha₂
                  ⟨z₂, hz₂d, hz₂a, hz₂b⟩ ?_ ?_]
              · intro y hy hya
                exact hmin₂ y ((hD1 y (by omega) (by omega)).mp hy) hya
              · intro z hz hza
                exact hmax₂ z ((hD1 z (by omega) (by omega)).mp hz) hza
          · -- nothing above w.1 anywhere
            have hwgt : σ.a + 1 < w.1 := by
              by_cases h : w.1 < σ.a
              · exact absurd ⟨σ, hσmem, h⟩ hab
              · omega
            rw [transInd_eq_zero_of_no_next Fm w (fun y hy h => hab ⟨y, hy, h⟩),
              transInd_eq_zero_of_no_next Fd w (fun y hy h => hab
                ⟨y, (hD1 y (by omega) (by omega)).mp hy, h⟩)]
        · rw [transInd_eq_zero Fm w (fun x hx hxa => hsrc ⟨x, hx, hxa⟩),
            transInd_eq_zero Fd w (fun x hx hxa => hsrc
              ⟨x, (hD1 x (by omega) (by omega)).mp hx, hxa⟩)]
      rw [htop, htrans]
      simp only [pair_eq_iff]
      split_ifs <;> omega

/-! ## Residual counts as fiber sums -/

/-- Count over a `flatMap` is the sum of per-piece counts. -/
lemma count_flatMap_pairs (f : ℕ → List (ℤ × ℤ)) : ∀ (l : List ℕ) (w : ℤ × ℤ),
    (l.flatMap f).count w = (l.map (fun d => (f d).count w)).sum := by
  intro l
  induction l with
  | nil => intro w; simp
  | cons d ds ih =>
    intro w
    rw [List.flatMap_cons, List.count_append, List.map_cons, List.sum_cons, ih w]

/-- The coordinate count of the RSK residual is the sum of derived-pair counts over
the fibers. -/
lemma count_residual_pairs (M : Multisegment) (w : ℤ × ℤ) :
    ((RSK.residual M).segments.map segPair).count w =
      ((List.range (RSK.maxDepth M + 1)).map
        (fun d => (derivedPairs ((bucket M d).map (·.val))).count w)).sum := by
  simp only [RSK.residual]
  rw [((List.perm_insertionSort (· ≤ ·) _).map segPair).count_eq]
  have hmapflat : ∀ (l : List ℕ),
      ((l.flatMap (fun d => RSK.bucketResidual M d)).map segPair)
        = l.flatMap (fun d => (RSK.bucketResidual M d).map segPair) := by
    intro l
    induction l with
    | nil => rfl
    | cons d ds ih => rw [List.flatMap_cons, List.flatMap_cons, List.map_append, ih]
  rw [hmapflat, count_flatMap_pairs (fun d => (RSK.bucketResidual M d).map segPair)]
  congr 1
  apply List.map_congr_left
  intro d _
  rw [bucketResidual_pairs]

/-! ## Non-chain fibers are untouched -/

/-- At a depth carrying no chain element, the `m†` fiber equals the `m` fiber
(count form). -/
lemma fiber_count_nonchain (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a)
    (d : ℕ)
    (hd : ∀ c ∈ (MW.leadingChain m).val.segments, ∀ hcm : c ∈ m.segments,
      depth_of_segment m c hcm ≠ d)
    (x : Segment) :
    ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments) d).map (·.val)).count x
      = ((bucket m d).map (·.val)).count x := by
  classical
  have hcount := count_mdag_full m x
  have hBlt := leadingChain_begins_lt m
  have hCsub : ∀ c ∈ (MW.leadingChain m).val.segments, c ∈ m.segments :=
    fun c hc => MW.leadingChain_subset m c hc
  by_cases hxC : x ∈ (MW.leadingChain m).val.segments
  · -- a chain value: off this fiber on both sides
    have hxm := hCsub x hxC
    have hend : depth_of_segment m x hxm ≠ d := hd x hxC hxm
    rw [bucket_count_eq_zero_of_depth_ne m _ x (fun hxm2 h => by
      have : depth_of_segment m x hxm2 = depth_of_segment m x hxm := rfl
      omega)]
    apply bucket_count_eq_zero_of_depth_ne
    intro hx'
    rw [mdag_depth_survivor m sₘ s_l hsₘ hs_l hmin x hxm hx' ?_]
    · exact hend
    · rintro ⟨σw, hσwC, hσwm, hwa, hwb, -⟩
      have := begin_unique_of_pairwise_lt _ hBlt σw hσwC x hxC (by omega)
      rw [this] at hwb
      omega
  · by_cases hstt : ∃ c ∈ (MW.leadingChain m).val.segments,
        c.a < c.b ∧ x.a = c.a + 1 ∧ x.b = c.b
    · -- a starred value: off this fiber on both sides
      obtain ⟨c, hcC, hcnd, hxa, hxb⟩ := hstt
      have hcm := hCsub c hcC
      have hdc : depth_of_segment m c hcm ≠ d := hd c hcC hcm
      have hx' : x ∈ (MW.makeResidual m
          (MW.leadingChain m).val.segments).segments := by
        rw [← List.count_pos_iff]
        rw [if_neg hxC, if_pos ⟨c, hcC, hcnd, hxa, hxb⟩] at hcount
        omega
      have hdd := mdag_depth_starred' m sₘ s_l hsₘ hs_l hmin c hcC hcm hcnd
        x hxa hxb hx'
      have hB : ((bucket (MW.makeResidual m
          (MW.leadingChain m).val.segments) d).map (·.val)).count x = 0 := by
        apply bucket_count_eq_zero_of_depth_ne
        intro hx'2
        have hpi : depth_of_segment (MW.makeResidual m
            (MW.leadingChain m).val.segments) x hx'2
            = depth_of_segment (MW.makeResidual m
            (MW.leadingChain m).val.segments) x hx' := rfl
        omega
      rw [hB]
      symm
      apply bucket_count_eq_zero_of_depth_ne
      intro hxm hxd
      have hge := depth_mdag_ge_notC m sₘ s_l hsₘ hs_l hmin x hxm hxC hx'
      have hub := (mdag_depth_bound m sₘ s_l hsₘ hs_l hmin _).1 x hxm hx' rfl
      obtain ⟨σw, hσwC, hσwm, hwa, hwb, hwd⟩ := hub.2 (by omega)
      exact hd σw hσwC hσwm (by omega)
    · rw [if_neg hxC, if_neg hstt] at hcount
      by_cases hxm : x ∈ m.segments
      · by_cases hsp : ∃ σw ∈ (MW.leadingChain m).val.segments,
            ∃ hσwm : σw ∈ m.segments, x.a = σw.a ∧ x.b < σw.b ∧
            depth_of_segment m x hxm = depth_of_segment m σw hσwm
        · -- special: off this fiber on both sides
          obtain ⟨σw, hσwC, hσwm, hwa, hwb, hwd⟩ := hsp
          have hdw : depth_of_segment m σw hσwm ≠ d := hd σw hσwC hσwm
          have hB1 : ((bucket m d).map (·.val)).count x = 0 :=
            bucket_count_eq_zero_of_depth_ne m _ x (fun hxm2 h => by
              have : depth_of_segment m x hxm2 = depth_of_segment m x hxm := rfl
              omega)
          rw [hB1]
          apply bucket_count_eq_zero_of_depth_ne
          intro hx'
          have hdep := special_moves_up m sₘ s_l hsₘ hs_l hmin x hxm hx'
            σw hσwC hσwm hwa hwb hwd
          intro hcon
          have hheadne : (MW.leadingChain m).val.segments.head? ≠ some σw := by
            rw [MW.leadingChain_head m sₘ hsₘ]
            intro h
            have heq := Option.some.inj h
            have ha := congrArg Segment.a heq
            have hb := congrArg Segment.b heq
            simp only [] at ha hb
            exact no_special_head m sₘ hsₘ x hxm (by omega) (by omega)
          obtain ⟨u₂, σp, v₂, hsplit₂⟩ :=
            exists_pred_split (MW.leadingChain m).val.segments σw hσwC hheadne
          have hσpC : σp ∈ (MW.leadingChain m).val.segments := by
            rw [hsplit₂]; simp
          have hσpm := hCsub σp hσpC
          have hgap := special_witness_gap m sₘ s_l hsₘ hs_l hmin x hxm
            σw hσwm hwa hwb hwd u₂ v₂ σp hsplit₂ hσpm
          exact hd σp hσpC hσpm (by omega)
        · -- plain: depth preserved, counts equal
          have hx' : x ∈ (MW.makeResidual m
              (MW.leadingChain m).val.segments).segments :=
            survivor_mem_mdag m _ x hxm hxC
          have hdep := mdag_depth_survivor m sₘ s_l hsₘ hs_l hmin x hxm hx' hsp
          by_cases hf : depth_of_segment m x hxm = d
          · rw [bucket_count_eq_of_depth m _ x (fun hxm2 => by
              have : depth_of_segment m x hxm2 = depth_of_segment m x hxm := rfl
              omega)]
            rw [bucket_count_eq_of_depth _ _ x (fun hx'2 => by
              have hpi : depth_of_segment (MW.makeResidual m
                  (MW.leadingChain m).val.segments) x hx'2
                  = depth_of_segment (MW.makeResidual m
                  (MW.leadingChain m).val.segments) x hx' := rfl
              omega)]
            omega
          · rw [bucket_count_eq_zero_of_depth_ne m _ x (fun hxm2 h => by
              have : depth_of_segment m x hxm2 = depth_of_segment m x hxm := rfl
              omega)]
            apply bucket_count_eq_zero_of_depth_ne
            intro hx'2
            have hpi : depth_of_segment (MW.makeResidual m
                (MW.leadingChain m).val.segments) x hx'2
                = depth_of_segment (MW.makeResidual m
                (MW.leadingChain m).val.segments) x hx' := rfl
            omega
      · have hB : ((bucket (MW.makeResidual m
            (MW.leadingChain m).val.segments) d).map (·.val)).count x = 0 := by
          apply bucket_count_eq_zero_of_depth_ne
          intro hx'
          have := List.count_pos_iff.mpr hx'
          have hzero : m.segments.count x = 0 := List.count_eq_zero.mpr hxm
          omega
        rw [hB, bucket_count_eq_zero_of_depth_ne m _ x (fun hxm2 _ => hxm hxm2)]

/-- At a non-chain depth the fiber lists coincide. -/
lemma fiber_list_nonchain_eq (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a)
    (d : ℕ)
    (hd : ∀ c ∈ (MW.leadingChain m).val.segments, ∀ hcm : c ∈ m.segments,
      depth_of_segment m c hcm ≠ d) :
    ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments) d).map (·.val))
      = ((bucket m d).map (·.val)) := by
  classical
  refine (List.perm_iff_count.mpr
      (fun x => fiber_count_nonchain m sₘ s_l hsₘ hs_l hmin d hd x)).eq_of_pairwise
    ?_ (bucket_nested _ d) (bucket_nested m d)
  intro a b _ _ h1 h2
  obtain ⟨a1, b1⟩ := h1
  obtain ⟨a2, b2⟩ := h2
  exact seg_ext (by omega) (by omega)

/-! ## Pair-level transfer and the per-fiber derived-count identity -/

lemma count_map_segPair_eq (L : List Segment) (x : Segment) :
    (L.map segPair).count (segPair x) = L.count x :=
  List.count_map_of_injective _ _ segPair_inj _

lemma count_map_segPair_illformed (L : List Segment) (w : ℤ × ℤ) (h : w.2 < w.1) :
    (L.map segPair).count w = 0 := by
  rw [List.count_eq_zero]
  intro hmem
  obtain ⟨x, hx, hfx⟩ := List.mem_map.mp hmem
  have h1 : x.a = w.1 := by rw [← hfx]; rfl
  have h2 : x.b = w.2 := by rw [← hfx]; rfl
  have h3 : x.a ≤ x.b := x.fst_le_snd
  omega

lemma derivedPairs_count_illformed (L : List Segment)
    (hs : L.Pairwise (fun s t => s.a ≤ t.a ∧ t.b ≤ s.b)) (w : ℤ × ℤ)
    (h : w.2 < w.1) : (derivedPairs L).count w = 0 := by
  rw [List.count_eq_zero]
  intro hmem
  obtain ⟨⟨s, t⟩, hpair, hfw⟩ := List.mem_map.mp hmem
  obtain ⟨l₁, l₂, hsplit⟩ := zip_tail_split L s t hpair
  rw [hsplit] at hs
  have hst := (List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).1 t (by simp)
  have h1 : s.a = w.1 := by rw [← hfw]
  have h2 : t.b = w.2 := by rw [← hfw]
  have h3 : t.a ≤ t.b := t.fst_le_snd
  obtain ⟨h4, -⟩ := hst
  omega

/-- **Per-fiber derived-count identity, chain step** (paper eqs. `sc2`/`sc3`): at `σ`'s
fiber, the derived pairs of `m†` are those of `m` with `W = ⟨σ.a, t.b⟩` replaced by
`⁻W = ⟨σ.a+1, t.b⟩`, the incoming specials of `σ'` added and the outgoing specials of
`σ` removed. -/
lemma derived_count_chain_step (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a)
    (u v : List Segment) (σ σ' : Segment)
    (hsplit : (MW.leadingChain m).val.segments = u ++ σ :: σ' :: v)
    (hσm : σ ∈ m.segments) (hσ'm : σ' ∈ m.segments)
    (i t : Segment) (l₁ l₂ : List Segment)
    (hbsplit : (bucket m (depth_of_segment m σ hσm)).map (·.val) = l₁ ++ i :: t :: l₂)
    (hia : i.a = σ.a) (hta : σ.a < t.a)
    (w : ℤ × ℤ) :
    (derivedPairs ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
        (depth_of_segment m σ hσm)).map (·.val))).count w
      + (if w = ((σ.a : ℤ), (t.b : ℤ)) then 1 else 0)
      + (if w.1 = σ.a ∧ w.2 < σ.b
         then (((bucket m (depth_of_segment m σ hσm)).map (·.val)).map segPair).count w
         else 0)
    = (derivedPairs ((bucket m (depth_of_segment m σ hσm)).map (·.val))).count w
      + (if w = ((σ.a + 1 : ℤ), (t.b : ℤ)) then 1 else 0)
      + (if w.1 = σ'.a ∧ w.2 < σ'.b
         then (((bucket m (depth_of_segment m σ' hσ'm)).map (·.val)).map segPair).count w
         else 0) := by
  classical
  have hσC : σ ∈ (MW.leadingChain m).val.segments := by rw [hsplit]; simp
  obtain ⟨⟨hlla, hllb⟩, hsucc⟩ := leadingChain_consecutive_link m u v σ σ' hsplit
  have hnd : σ.a < σ.b := chain_seg_nondegenerate m sₘ s_l hsₘ hs_l hmin σ hσC
  have htb : t.a ≤ t.b := t.fst_le_snd
  have hFdsort : ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
      (depth_of_segment m σ hσm)).map (·.val)).Pairwise
      (fun s t => s.a ≤ t.a ∧ t.b ≤ s.b) :=
    (bucket_nested _ _).imp (fun h => ⟨h.1, h.2⟩)
  have hFmsort : ((bucket m (depth_of_segment m σ hσm)).map (·.val)).Pairwise
      (fun s t => s.a ≤ t.a ∧ t.b ≤ s.b) :=
    (bucket_nested m _).imp (fun h => ⟨h.1, h.2⟩)
  by_cases hwf : w.1 ≤ w.2
  · -- w names a genuine segment
    set x : Segment := ⟨⟨w.1, w.2⟩, hwf⟩ with hxdef
    have hxa : x.a = w.1 := rfl
    have hxb : x.b = w.2 := rfl
    have hxw : segPair x = w := rfl
    have hE1 := fiber_count_chain_step m sₘ s_l hsₘ hs_l hmin u v σ σ' hsplit
      hσm hσ'm x
    -- convert E1 to pair counts
    have hcd : (((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
        (depth_of_segment m σ hσm)).map (·.val)).map segPair).count w
        = ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
        (depth_of_segment m σ hσm)).map (·.val)).count x := by
      rw [← hxw, count_map_segPair_eq]
    have hcm : (((bucket m (depth_of_segment m σ hσm)).map (·.val)).map segPair).count w
        = ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count x := by
      rw [← hxw, count_map_segPair_eq]
    have hcm' : (((bucket m (depth_of_segment m σ' hσ'm)).map (·.val)).map segPair).count w
        = ((bucket m (depth_of_segment m σ' hσ'm)).map (·.val)).count x := by
      rw [← hxw, count_map_segPair_eq]
    -- E1 at pair level
    have hE1p : (((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
        (depth_of_segment m σ hσm)).map (·.val)).map segPair).count w
        + (if w = ((σ.a : ℤ), (σ.b : ℤ)) then 1 else 0)
        + (if w.1 = σ.a ∧ w.2 < σ.b
           then (((bucket m (depth_of_segment m σ hσm)).map (·.val)).map segPair).count w
           else 0)
        = (((bucket m (depth_of_segment m σ hσm)).map (·.val)).map segPair).count w
        + (if w = ((σ.a + 1 : ℤ), (σ.b : ℤ)) then 1 else 0)
        + (if w.1 = σ'.a ∧ w.2 < σ'.b
           then (((bucket m (depth_of_segment m σ' hσ'm)).map (·.val)).map segPair).count w
           else 0) := by
      rw [hcd, hcm, hcm']
      have e1 : (w = ((σ.a : ℤ), (σ.b : ℤ))) ↔ (x = σ) := by
        rw [pair_eq_iff]
        constructor
        · rintro ⟨h1, h2⟩; exact seg_ext (by omega) (by omega)
        · intro h
          have ha := congrArg Segment.a h
          have hb := congrArg Segment.b h
          simp only [] at ha hb
          omega
      have e2 : (w = ((σ.a + 1 : ℤ), (σ.b : ℤ))) ↔ (x.a = σ.a + 1 ∧ x.b = σ.b) := by
        rw [pair_eq_iff]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
        · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
      have e3 : (w.1 = σ.a ∧ w.2 < σ.b) ↔ (x.a = σ.a ∧ x.b < σ.b) := by
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
        · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
      have e4 : (w.1 = σ'.a ∧ w.2 < σ'.b) ↔ (x.a = σ'.a ∧ x.b < σ'.b) := by
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
        · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
      simp only [e1, e2, e3, e4]
      exact hE1
    -- characterizations of both derived-pair counts
    have hcharD := derivedPairs_count w _ hFdsort
    have hcharM := derivedPairs_count w _ hFmsort
    -- indicator transport hypotheses
    have hIND := indicator_transport
      ((bucket m (depth_of_segment m σ hσm)).map (·.val))
      ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
        (depth_of_segment m σ hσm)).map (·.val))
      σ t
      (RSK.mem_bucket_of_depth m _ σ hσm rfl) hta (by rw [hbsplit]; simp)
      (fun y hy hya => boundary_next_facts m _ i t l₁ l₂ hbsplit y hy (by omega))
      ?_ ?_ ?_ ?_ ?_ w
    · omega
    · -- A1: the new σ-group sits inside the old one, ending at or after σ
      intro y hy hya
      have hyc : 0 < ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
          (depth_of_segment m σ hσm)).map (·.val)).count y := List.count_pos_iff.mpr hy
      have hy1 := fiber_count_chain_step m sₘ s_l hsₘ hs_l hmin u v σ σ' hsplit
        hσm hσ'm y
      have hn3 : ¬(y.a = σ.a + 1 ∧ y.b = σ.b) := by rintro ⟨h1, -⟩; omega
      have hn4 : ¬(y.a = σ'.a ∧ y.b < σ'.b) := by rintro ⟨h1, -⟩; omega
      rw [if_neg hn3, if_neg hn4] at hy1
      by_cases hyσ : y = σ
      · subst hyσ
        exact ⟨RSK.mem_bucket_of_depth m _ y hσm rfl, le_refl _⟩
      · rw [if_neg hyσ] at hy1
        by_cases hyb : y.b < σ.b
        · rw [if_pos ⟨hya, hyb⟩] at hy1
          omega
        · have hn2 : ¬(y.a = σ.a ∧ y.b < σ.b) := by rintro ⟨-, h⟩; omega
          rw [if_neg hn2] at hy1
          exact ⟨List.count_pos_iff.mp (by omega), by omega⟩
    · -- A2: old strictly-longer group members survive
      intro y hy hya hyb
      have hyc : 0 < ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count y :=
        List.count_pos_iff.mpr hy
      have hy1 := fiber_count_chain_step m sₘ s_l hsₘ hs_l hmin u v σ σ' hsplit
        hσm hσ'm y
      have hn1 : y ≠ σ := fun h => by
        have hb := congrArg Segment.b h
        simp only [] at hb
        omega
      have hn2 : ¬(y.a = σ.a ∧ y.b < σ.b) := by rintro ⟨-, h⟩; omega
      have hn3 : ¬(y.a = σ.a + 1 ∧ y.b = σ.b) := by rintro ⟨h, -⟩; omega
      have hn4 : ¬(y.a = σ'.a ∧ y.b < σ'.b) := by rintro ⟨h, -⟩; omega
      rw [if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4] at hy1
      exact List.count_pos_iff.mp (by omega)
    · -- B1: the starred value is present
      have hstep : σ.a + 1 ≤ σ.b := by omega
      refine ⟨⟨⟨σ.a + 1, σ.b⟩, hstep⟩, ?_, rfl, rfl⟩
      have hy1 := fiber_count_chain_step m sₘ s_l hsₘ hs_l hmin u v σ σ' hsplit
        hσm hσ'm ⟨⟨σ.a + 1, σ.b⟩, hstep⟩
      have hga : Segment.a (⟨⟨σ.a + 1, σ.b⟩, hstep⟩ : Segment) = σ.a + 1 := rfl
      have hgb : Segment.b (⟨⟨σ.a + 1, σ.b⟩, hstep⟩ : Segment) = σ.b := rfl
      have hn1 : (⟨⟨σ.a + 1, σ.b⟩, hstep⟩ : Segment) ≠ σ := fun h => by
        have ha := congrArg Segment.a h
        simp only [] at ha
        omega
      have hn2 : ¬(Segment.a (⟨⟨σ.a + 1, σ.b⟩, hstep⟩ : Segment) = σ.a ∧
          Segment.b (⟨⟨σ.a + 1, σ.b⟩, hstep⟩ : Segment) < σ.b) := by
        rintro ⟨h, -⟩
        omega
      have hp3 : Segment.a (⟨⟨σ.a + 1, σ.b⟩, hstep⟩ : Segment) = σ.a + 1 ∧
          Segment.b (⟨⟨σ.a + 1, σ.b⟩, hstep⟩ : Segment) = σ.b := ⟨hga, hgb⟩
      have hp4 : Segment.a (⟨⟨σ.a + 1, σ.b⟩, hstep⟩ : Segment) = σ'.a ∧
          Segment.b (⟨⟨σ.a + 1, σ.b⟩, hstep⟩ : Segment) < σ'.b := ⟨by omega, by omega⟩
      rw [if_neg hn1, if_neg hn2, if_pos hp3, if_pos hp4] at hy1
      exact List.count_pos_iff.mp (by omega)
    · -- B2: the new successor group ends at or before σ
      intro y hy hya
      have hyc : 0 < ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
          (depth_of_segment m σ hσm)).map (·.val)).count y := List.count_pos_iff.mpr hy
      have hy1 := fiber_count_chain_step m sₘ s_l hsₘ hs_l hmin u v σ σ' hsplit
        hσm hσ'm y
      have hn1 : y ≠ σ := fun h => by
        have ha := congrArg Segment.a h
        simp only [] at ha
        omega
      have hn2 : ¬(y.a = σ.a ∧ y.b < σ.b) := by rintro ⟨h, -⟩; omega
      rw [if_neg hn1, if_neg hn2] at hy1
      by_cases hyb : y.b = σ.b
      · omega
      · have hn3 : ¬(y.a = σ.a + 1 ∧ y.b = σ.b) := by rintro ⟨-, h⟩; omega
        rw [if_neg hn3] at hy1
        by_cases hyJ : y.a = σ'.a ∧ y.b < σ'.b
        · rw [if_pos hyJ] at hy1
          by_cases hym0 : 0 < ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count y
          · obtain ⟨hym, hyd⟩ := RSK.mem_bucket_depth m _ y (List.count_pos_iff.mp hym0)
            exact fiber_succ_end_le m σ hσm y hym hya hyd
          · have hyJ0 : 0 < ((bucket m
                (depth_of_segment m σ' hσ'm)).map (·.val)).count y := by omega
            obtain ⟨hym, -⟩ := RSK.mem_bucket_depth m _ y (List.count_pos_iff.mp hyJ0)
            exact special_end_le_pred m u v σ σ' hsplit y hym hyJ.1 hyJ.2
        · rw [if_neg hyJ] at hy1
          have hym0 : 0 < ((bucket m
              (depth_of_segment m σ hσm)).map (·.val)).count y := by omega
          obtain ⟨hym, hyd⟩ := RSK.mem_bucket_depth m _ y (List.count_pos_iff.mp hym0)
          exact fiber_succ_end_le m σ hσm y hym hya hyd
    · -- D1: other begin-groups are untouched
      intro y hy1a hy2a
      have hy1 := fiber_count_chain_step m sₘ s_l hsₘ hs_l hmin u v σ σ' hsplit
        hσm hσ'm y
      have hn1 : y ≠ σ := fun h => hy1a (by rw [h])
      have hn2 : ¬(y.a = σ.a ∧ y.b < σ.b) := by rintro ⟨h, -⟩; exact hy1a h
      have hn3 : ¬(y.a = σ.a + 1 ∧ y.b = σ.b) := by rintro ⟨h, -⟩; exact hy2a h
      have hn4 : ¬(y.a = σ'.a ∧ y.b < σ'.b) := by rintro ⟨h, -⟩; omega
      rw [if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4] at hy1
      constructor
      · intro hy
        have := List.count_pos_iff.mpr hy
        exact List.count_pos_iff.mp (by omega)
      · intro hy
        have := List.count_pos_iff.mpr hy
        exact List.count_pos_iff.mp (by omega)
  · -- ill-formed pairs contribute nothing anywhere
    push_neg at hwf
    have hnv1 : ¬(w = ((σ.a : ℤ), (t.b : ℤ))) := fun h => by
      rw [pair_eq_iff] at h
      omega
    have hnv2 : ¬(w = ((σ.a + 1 : ℤ), (t.b : ℤ))) := fun h => by
      rw [pair_eq_iff] at h
      omega
    rw [derivedPairs_count_illformed _ hFdsort w hwf,
      derivedPairs_count_illformed _ hFmsort w hwf,
      if_neg hnv1, if_neg hnv2]
    by_cases h1 : w.1 = σ.a ∧ w.2 < σ.b
    · rw [if_pos h1, count_map_segPair_illformed _ w hwf]
      by_cases h2 : w.1 = σ'.a ∧ w.2 < σ'.b
      · rw [if_pos h2, count_map_segPair_illformed _ w hwf]
      · rw [if_neg h2]
    · rw [if_neg h1]
      by_cases h2 : w.1 = σ'.a ∧ w.2 < σ'.b
      · rw [if_pos h2, count_map_segPair_illformed _ w hwf]
      · rw [if_neg h2]

/-- **Per-fiber derived-count identity, last chain element**: as
`derived_count_chain_step` without an incoming-specials term. -/
lemma derived_count_chain_last (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a)
    (u : List Segment) (σ : Segment)
    (hsplit : (MW.leadingChain m).val.segments = u ++ [σ])
    (hσm : σ ∈ m.segments)
    (i t : Segment) (l₁ l₂ : List Segment)
    (hbsplit : (bucket m (depth_of_segment m σ hσm)).map (·.val) = l₁ ++ i :: t :: l₂)
    (hia : i.a = σ.a) (hta : σ.a < t.a)
    (w : ℤ × ℤ) :
    (derivedPairs ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
        (depth_of_segment m σ hσm)).map (·.val))).count w
      + (if w = ((σ.a : ℤ), (t.b : ℤ)) then 1 else 0)
      + (if w.1 = σ.a ∧ w.2 < σ.b
         then (((bucket m (depth_of_segment m σ hσm)).map (·.val)).map segPair).count w
         else 0)
    = (derivedPairs ((bucket m (depth_of_segment m σ hσm)).map (·.val))).count w
      + (if w = ((σ.a + 1 : ℤ), (t.b : ℤ)) then 1 else 0) := by
  classical
  have hσC : σ ∈ (MW.leadingChain m).val.segments := by rw [hsplit]; simp
  have hnd : σ.a < σ.b := chain_seg_nondegenerate m sₘ s_l hsₘ hs_l hmin σ hσC
  have htb : t.a ≤ t.b := t.fst_le_snd
  have hFdsort : ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
      (depth_of_segment m σ hσm)).map (·.val)).Pairwise
      (fun s t => s.a ≤ t.a ∧ t.b ≤ s.b) :=
    (bucket_nested _ _).imp (fun h => ⟨h.1, h.2⟩)
  have hFmsort : ((bucket m (depth_of_segment m σ hσm)).map (·.val)).Pairwise
      (fun s t => s.a ≤ t.a ∧ t.b ≤ s.b) :=
    (bucket_nested m _).imp (fun h => ⟨h.1, h.2⟩)
  by_cases hwf : w.1 ≤ w.2
  · set x : Segment := ⟨⟨w.1, w.2⟩, hwf⟩ with hxdef
    have hxa : x.a = w.1 := rfl
    have hxb : x.b = w.2 := rfl
    have hxw : segPair x = w := rfl
    have hE1 := fiber_count_chain_last m sₘ s_l hsₘ hs_l hmin u σ hsplit hσm x
    have hcd : (((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
        (depth_of_segment m σ hσm)).map (·.val)).map segPair).count w
        = ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
        (depth_of_segment m σ hσm)).map (·.val)).count x := by
      rw [← hxw, count_map_segPair_eq]
    have hcm : (((bucket m (depth_of_segment m σ hσm)).map (·.val)).map segPair).count w
        = ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count x := by
      rw [← hxw, count_map_segPair_eq]
    have hE1p : (((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
        (depth_of_segment m σ hσm)).map (·.val)).map segPair).count w
        + (if w = ((σ.a : ℤ), (σ.b : ℤ)) then 1 else 0)
        + (if w.1 = σ.a ∧ w.2 < σ.b
           then (((bucket m (depth_of_segment m σ hσm)).map (·.val)).map segPair).count w
           else 0)
        = (((bucket m (depth_of_segment m σ hσm)).map (·.val)).map segPair).count w
        + (if w = ((σ.a + 1 : ℤ), (σ.b : ℤ)) then 1 else 0) := by
      rw [hcd, hcm]
      have e1 : (w = ((σ.a : ℤ), (σ.b : ℤ))) ↔ (x = σ) := by
        rw [pair_eq_iff]
        constructor
        · rintro ⟨h1, h2⟩; exact seg_ext (by omega) (by omega)
        · intro h
          have ha := congrArg Segment.a h
          have hb := congrArg Segment.b h
          simp only [] at ha hb
          omega
      have e2 : (w = ((σ.a + 1 : ℤ), (σ.b : ℤ))) ↔ (x.a = σ.a + 1 ∧ x.b = σ.b) := by
        rw [pair_eq_iff]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
        · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
      have e3 : (w.1 = σ.a ∧ w.2 < σ.b) ↔ (x.a = σ.a ∧ x.b < σ.b) := by
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
        · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
      simp only [e1, e2, e3]
      exact hE1
    have hcharD := derivedPairs_count w _ hFdsort
    have hcharM := derivedPairs_count w _ hFmsort
    have hIND := indicator_transport
      ((bucket m (depth_of_segment m σ hσm)).map (·.val))
      ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
        (depth_of_segment m σ hσm)).map (·.val))
      σ t
      (RSK.mem_bucket_of_depth m _ σ hσm rfl) hta (by rw [hbsplit]; simp)
      (fun y hy hya => boundary_next_facts m _ i t l₁ l₂ hbsplit y hy (by omega))
      ?_ ?_ ?_ ?_ ?_ w
    · omega
    · -- A1
      intro y hy hya
      have hyc : 0 < ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
          (depth_of_segment m σ hσm)).map (·.val)).count y := List.count_pos_iff.mpr hy
      have hy1 := fiber_count_chain_last m sₘ s_l hsₘ hs_l hmin u σ hsplit hσm y
      have hn3 : ¬(y.a = σ.a + 1 ∧ y.b = σ.b) := by rintro ⟨h1, -⟩; omega
      rw [if_neg hn3] at hy1
      by_cases hyσ : y = σ
      · subst hyσ
        exact ⟨RSK.mem_bucket_of_depth m _ y hσm rfl, le_refl _⟩
      · rw [if_neg hyσ] at hy1
        by_cases hyb : y.b < σ.b
        · rw [if_pos ⟨hya, hyb⟩] at hy1
          omega
        · have hn2 : ¬(y.a = σ.a ∧ y.b < σ.b) := by rintro ⟨-, h⟩; omega
          rw [if_neg hn2] at hy1
          exact ⟨List.count_pos_iff.mp (by omega), by omega⟩
    · -- A2
      intro y hy hya hyb
      have hyc : 0 < ((bucket m (depth_of_segment m σ hσm)).map (·.val)).count y :=
        List.count_pos_iff.mpr hy
      have hy1 := fiber_count_chain_last m sₘ s_l hsₘ hs_l hmin u σ hsplit hσm y
      have hn1 : y ≠ σ := fun h => by
        have hb := congrArg Segment.b h
        simp only [] at hb
        omega
      have hn2 : ¬(y.a = σ.a ∧ y.b < σ.b) := by rintro ⟨-, h⟩; omega
      have hn3 : ¬(y.a = σ.a + 1 ∧ y.b = σ.b) := by rintro ⟨h, -⟩; omega
      rw [if_neg hn1, if_neg hn2, if_neg hn3] at hy1
      exact List.count_pos_iff.mp (by omega)
    · -- B1
      have hstep : σ.a + 1 ≤ σ.b := by omega
      refine ⟨⟨⟨σ.a + 1, σ.b⟩, hstep⟩, ?_, rfl, rfl⟩
      have hy1 := fiber_count_chain_last m sₘ s_l hsₘ hs_l hmin u σ hsplit hσm
        ⟨⟨σ.a + 1, σ.b⟩, hstep⟩
      have hga : Segment.a (⟨⟨σ.a + 1, σ.b⟩, hstep⟩ : Segment) = σ.a + 1 := rfl
      have hgb : Segment.b (⟨⟨σ.a + 1, σ.b⟩, hstep⟩ : Segment) = σ.b := rfl
      have hn1 : (⟨⟨σ.a + 1, σ.b⟩, hstep⟩ : Segment) ≠ σ := fun h => by
        have ha := congrArg Segment.a h
        simp only [] at ha
        omega
      have hn2 : ¬(Segment.a (⟨⟨σ.a + 1, σ.b⟩, hstep⟩ : Segment) = σ.a ∧
          Segment.b (⟨⟨σ.a + 1, σ.b⟩, hstep⟩ : Segment) < σ.b) := by
        rintro ⟨h, -⟩
        omega
      have hp3 : Segment.a (⟨⟨σ.a + 1, σ.b⟩, hstep⟩ : Segment) = σ.a + 1 ∧
          Segment.b (⟨⟨σ.a + 1, σ.b⟩, hstep⟩ : Segment) = σ.b := ⟨hga, hgb⟩
      rw [if_neg hn1, if_neg hn2, if_pos hp3] at hy1
      exact List.count_pos_iff.mp (by omega)
    · -- B2
      intro y hy hya
      have hyc : 0 < ((bucket (MW.makeResidual m (MW.leadingChain m).val.segments)
          (depth_of_segment m σ hσm)).map (·.val)).count y := List.count_pos_iff.mpr hy
      have hy1 := fiber_count_chain_last m sₘ s_l hsₘ hs_l hmin u σ hsplit hσm y
      have hn1 : y ≠ σ := fun h => by
        have ha := congrArg Segment.a h
        simp only [] at ha
        omega
      have hn2 : ¬(y.a = σ.a ∧ y.b < σ.b) := by rintro ⟨h, -⟩; omega
      rw [if_neg hn1, if_neg hn2] at hy1
      by_cases hyb : y.b = σ.b
      · omega
      · have hn3 : ¬(y.a = σ.a + 1 ∧ y.b = σ.b) := by rintro ⟨-, h⟩; omega
        rw [if_neg hn3] at hy1
        have hym0 : 0 < ((bucket m
            (depth_of_segment m σ hσm)).map (·.val)).count y := by omega
        obtain ⟨hym, hyd⟩ := RSK.mem_bucket_depth m _ y (List.count_pos_iff.mp hym0)
        exact fiber_succ_end_le m σ hσm y hym hya hyd
    · -- D1
      intro y hy1a hy2a
      have hy1 := fiber_count_chain_last m sₘ s_l hsₘ hs_l hmin u σ hsplit hσm y
      have hn1 : y ≠ σ := fun h => hy1a (by rw [h])
      have hn2 : ¬(y.a = σ.a ∧ y.b < σ.b) := by rintro ⟨h, -⟩; exact hy1a h
      have hn3 : ¬(y.a = σ.a + 1 ∧ y.b = σ.b) := by rintro ⟨h, -⟩; exact hy2a h
      rw [if_neg hn1, if_neg hn2, if_neg hn3] at hy1
      constructor
      · intro hy
        have := List.count_pos_iff.mpr hy
        exact List.count_pos_iff.mp (by omega)
      · intro hy
        have := List.count_pos_iff.mpr hy
        exact List.count_pos_iff.mp (by omega)
  · push_neg at hwf
    have hnv1 : ¬(w = ((σ.a : ℤ), (t.b : ℤ))) := fun h => by
      rw [pair_eq_iff] at h
      omega
    have hnv2 : ¬(w = ((σ.a + 1 : ℤ), (t.b : ℤ))) := fun h => by
      rw [pair_eq_iff] at h
      omega
    rw [derivedPairs_count_illformed _ hFdsort w hwf,
      derivedPairs_count_illformed _ hFmsort w hwf,
      if_neg hnv1, if_neg hnv2]
    by_cases h1 : w.1 = σ.a ∧ w.2 < σ.b
    · rw [if_pos h1, count_map_segPair_illformed _ w hwf]
    · rw [if_neg h1]

/-- Permutations preserve sums of naturals. -/
lemma sum_perm_nat : ∀ {l₁ l₂ : List ℕ}, l₁.Perm l₂ → l₁.sum = l₂.sum := by
  intro l₁ l₂ h
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [List.sum_cons, ih]
  | swap x y l => simp only [List.sum_cons]; omega
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

/-- **The telescoping identity** (paper eq. `deltau`, value form): summed over all
fibers, the derived pairs of `m†` are those of `m` with each residual-chain value `Wⱼ`
replaced by its left-shortened copy `⁻Wⱼ`. Stated against the leading chain of the RSK
residual, whose entries are exactly the `Wⱼ` (`leadingChain_residual_entries`). -/
lemma residual_count_telescope (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a)
    (w : ℤ × ℤ) :
    ((List.range (RSK.maxDepth m + 1)).map
        (fun d => (derivedPairs ((bucket (MW.makeResidual m
          (MW.leadingChain m).val.segments) d).map (·.val))).count w)).sum
      + ((MW.leadingChain (RSK.residual m)).val.segments.map
          (fun c => if w = segPair c then 1 else 0)).sum
    = ((List.range (RSK.maxDepth m + 1)).map
        (fun d => (derivedPairs ((bucket m d).map (·.val))).count w)).sum
      + ((MW.leadingChain (RSK.residual m)).val.segments.map
          (fun c => if w = ((c.a + 1 : ℤ), (c.b : ℤ)) then 1 else 0)).sum := by
  classical
  have hlen := chainLenPreserved m sₘ s_l hsₘ hs_l hmin
  have hBlt := leadingChain_begins_lt m
  -- the incoming-specials term carried by the head of the remaining chain
  have haux : ∀ (cs : List Segment), ∀ (pre : List Segment),
      (MW.leadingChain m).val.segments = pre ++ cs →
      ∀ (cs' pre' : List Segment),
      (MW.leadingChain (RSK.residual m)).val.segments = pre' ++ cs' →
      pre'.length = pre.length →
      ∀ (R : List ℕ), R.Nodup →
      (∀ c ∈ cs, ∀ hcm : c ∈ m.segments, depth_of_segment m c hcm ∈ R) →
      (∀ d ∈ R, ∀ c ∈ pre, ∀ hcm : c ∈ m.segments, depth_of_segment m c hcm ≠ d) →
      (R.map (fun d => (derivedPairs ((bucket (MW.makeResidual m
          (MW.leadingChain m).val.segments) d).map (·.val))).count w)).sum
        + (cs'.map (fun c => if w = segPair c then 1 else 0)).sum
        + (cs.head?.elim 0 (fun σ =>
            if hm : σ ∈ m.segments then
              (if w.1 = σ.a ∧ w.2 < σ.b
               then (((bucket m (depth_of_segment m σ hm)).map (·.val)).map
                 segPair).count w
               else 0)
            else 0))
      = (R.map (fun d => (derivedPairs ((bucket m d).map (·.val))).count w)).sum
        + (cs'.map (fun c => if w = ((c.a + 1 : ℤ), (c.b : ℤ)) then 1 else 0)).sum := by
    intro cs
    induction cs with
    | nil =>
      intro pre hsplitC cs' pre' hsplitC' hlen' R hnd hin hout
      have hcs' : cs' = [] := by
        have h1 : (MW.leadingChain (RSK.residual m)).val.segments.length
            = pre'.length + cs'.length := by rw [hsplitC']; simp
        have h2 : (MW.leadingChain m).val.segments.length = pre.length := by
          rw [hsplitC]; simp
        have h3 : cs'.length = 0 := by omega
        exact List.eq_nil_of_length_eq_zero h3
      subst hcs'
      simp only [List.map_nil, List.sum_nil, List.head?_nil, Option.elim]
      have hcong : ∀ d ∈ R,
          (derivedPairs ((bucket (MW.makeResidual m
            (MW.leadingChain m).val.segments) d).map (·.val))).count w
          = (derivedPairs ((bucket m d).map (·.val))).count w := by
        intro d hd
        rw [fiber_list_nonchain_eq m sₘ s_l hsₘ hs_l hmin d ?_]
        intro c hc hcm
        rw [hsplitC] at hc
        simp only [List.append_nil] at hc
        exact hout d hd c hc hcm
      rw [List.map_congr_left hcong]
      omega
    | cons σ rest ih =>
      intro pre hsplitC cs' pre' hsplitC' hlen' R hnd hin hout
      -- align the residual chain
      obtain ⟨w', rest', hcs'⟩ : ∃ w' rest', cs' = w' :: rest' := by
        cases cs' with
        | nil =>
          exfalso
          have h1 : (MW.leadingChain (RSK.residual m)).val.segments.length
              = pre'.length := by rw [hsplitC']; simp
          have h2 : (MW.leadingChain m).val.segments.length
              = pre.length + rest.length + 1 := by rw [hsplitC]; simp; omega
          have := hlen
          omega
        | cons a b => exact ⟨a, b, rfl⟩
      subst hcs'
      have hσget : (MW.leadingChain m).val.segments[pre.length]? = some σ :=
        getElem?_of_split pre (rest) σ _ hsplitC
      have hw'get : (MW.leadingChain (RSK.residual m)).val.segments[pre.length]?
          = some w' := by
        rw [← hlen']
        exact getElem?_of_split pre' rest' w' _ hsplitC'
      obtain ⟨hσm, i, t, l₁, l₂, hbsplit, hia, hta, w'', hw''get, hw''a, hw''b⟩ :=
        leadingChain_residual_entries m sₘ s_l hsₘ hs_l hmin pre.length σ hσget
      have heqw : w'' = w' := by
        rw [hw'get] at hw''get
        exact (Option.some.inj hw''get).symm
      have hw'a : w'.a = σ.a := by rw [← heqw]; exact hw''a
      have hw'b : w'.b = t.b := by rw [← heqw]; exact hw''b
      have hσC : σ ∈ (MW.leadingChain m).val.segments := by rw [hsplitC]; simp
      have hdmem : depth_of_segment m σ hσm ∈ R := by
        have := hin σ List.mem_cons_self hσm
        exact this
      have hperm : R.Perm (depth_of_segment m σ hσm :: R.erase
          (depth_of_segment m σ hσm)) := List.perm_cons_erase hdmem
      have hndE : (R.erase (depth_of_segment m σ hσm)).Nodup := hnd.erase _
      -- value conversions for the two indicator terms
      have hW : ((σ.a : ℤ), (t.b : ℤ)) = segPair w' := by
        unfold segPair
        rw [hw'a, hw'b]
      have hBv : ((σ.a + 1 : ℤ), (t.b : ℤ)) = ((w'.a + 1 : ℤ), (w'.b : ℤ)) := by
        rw [hw'a, hw'b]
      -- unfold the head term at σ
      have hJσ : ((σ :: rest).head?.elim 0 (fun τ =>
          if hm : τ ∈ m.segments then
            (if w.1 = τ.a ∧ w.2 < τ.b
             then (((bucket m (depth_of_segment m τ hm)).map (·.val)).map
               segPair).count w
             else 0)
          else 0))
          = (if w.1 = σ.a ∧ w.2 < σ.b
             then (((bucket m (depth_of_segment m σ hσm)).map (·.val)).map
               segPair).count w
             else 0) := by
        simp only [List.head?_cons, Option.elim]
        rw [dif_pos hσm]
      -- sums split off the σ-fiber
      have hsumdag : (R.map (fun d => (derivedPairs ((bucket (MW.makeResidual m
          (MW.leadingChain m).val.segments) d).map (·.val))).count w)).sum
          = (derivedPairs ((bucket (MW.makeResidual m
              (MW.leadingChain m).val.segments)
              (depth_of_segment m σ hσm)).map (·.val))).count w
            + ((R.erase (depth_of_segment m σ hσm)).map
                (fun d => (derivedPairs ((bucket (MW.makeResidual m
                  (MW.leadingChain m).val.segments) d).map (·.val))).count w)).sum := by
        rw [sum_perm_nat (hperm.map _)]
        simp
      have hsumm : (R.map (fun d =>
          (derivedPairs ((bucket m d).map (·.val))).count w)).sum
          = (derivedPairs ((bucket m
              (depth_of_segment m σ hσm)).map (·.val))).count w
            + ((R.erase (depth_of_segment m σ hσm)).map (fun d =>
                (derivedPairs ((bucket m d).map (·.val))).count w)).sum := by
        rw [sum_perm_nat (hperm.map _)]
        simp
      cases rest with
      | nil =>
        -- last chain element
        have hid := derived_count_chain_last m sₘ s_l hsₘ hs_l hmin pre σ hsplitC hσm
          i t l₁ l₂ hbsplit hia hta w
        rw [hW, hBv] at hid
        have hihx := ih (pre ++ [σ]) (by rw [hsplitC, List.append_assoc]; rfl)
          rest' (pre' ++ [w']) (by rw [hsplitC', List.append_assoc]; rfl)
          (by simp; omega)
          (R.erase (depth_of_segment m σ hσm)) hndE
          (by intro c hc; simp at hc)
          ?_
        · rw [hJσ, hsumdag, hsumm]
          simp only [List.head?_nil, Option.elim] at hihx
          simp only [List.map_cons, List.sum_cons]
          omega
        · intro d hd c hc hcm
          rcases List.mem_append.mp hc with h1 | h2
          · exact hout d (List.mem_of_mem_erase hd) c h1 hcm
          · rw [List.mem_singleton] at h2
            subst h2
            have hne := (List.Nodup.mem_erase_iff hnd).mp hd
            intro heq
            have : depth_of_segment m c hcm = depth_of_segment m c hσm := rfl
            omega
      | cons σ' rest2 =>
        -- interior chain element: successor exists
        have hσ'C : σ' ∈ (MW.leadingChain m).val.segments := by rw [hsplitC]; simp
        have hσ'm : σ' ∈ m.segments := MW.leadingChain_subset m σ' hσ'C
        have hid := derived_count_chain_step m sₘ s_l hsₘ hs_l hmin pre rest2 σ σ'
          hsplitC hσm hσ'm i t l₁ l₂ hbsplit hia hta w
        rw [hW, hBv] at hid
        have hihx := ih (pre ++ [σ]) (by rw [hsplitC, List.append_assoc]; rfl)
          rest' (pre' ++ [w']) (by rw [hsplitC', List.append_assoc]; rfl)
          (by simp; omega)
          (R.erase (depth_of_segment m σ hσm)) hndE
          ?_ ?_
        · have hJσ' : ((σ' :: rest2).head?.elim 0 (fun τ =>
              if hm : τ ∈ m.segments then
                (if w.1 = τ.a ∧ w.2 < τ.b
                 then (((bucket m (depth_of_segment m τ hm)).map (·.val)).map
                   segPair).count w
                 else 0)
              else 0))
              = (if w.1 = σ'.a ∧ w.2 < σ'.b
                 then (((bucket m (depth_of_segment m σ' hσ'm)).map (·.val)).map
                   segPair).count w
                 else 0) := by
            simp only [List.head?_cons, Option.elim]
            rw [dif_pos hσ'm]
          rw [hJσ'] at hihx
          simp only [List.map_cons, List.sum_cons] at hihx ⊢
          rw [hJσ, hsumdag, hsumm]
          omega
        · intro c hc hcm
          have hcC : c ∈ (MW.leadingChain m).val.segments := by
            rw [hsplitC]
            exact List.mem_append_right _ (List.mem_cons_of_mem _ hc)
          have hcin := hin c (List.mem_cons_of_mem _ hc) hcm
          have hcane : c.a ≠ σ.a := by
            have hp := hBlt
            rw [hsplitC] at hp
            have hp2 := (List.pairwise_append.mp hp).2.1
            have := (List.pairwise_cons.mp hp2).1 c hc
            omega
          have hne := chain_mem_depth_ne m c σ hcC hσC hcane hcm hσm
          exact (List.mem_erase_of_ne hne).mpr hcin
        · intro d hd c hc hcm
          rcases List.mem_append.mp hc with h1 | h2
          · exact hout d (List.mem_of_mem_erase hd) c h1 hcm
          · rw [List.mem_singleton] at h2
            subst h2
            have hne := (List.Nodup.mem_erase_iff hnd).mp hd
            intro heq
            have : depth_of_segment m c hcm = depth_of_segment m c hσm := rfl
            omega
  -- outer application at the full chain and full depth range
  have hm : m.segments ≠ [] := by
    intro h
    rw [h] at hsₘ
    simp at hsₘ
  have hres := haux (MW.leadingChain m).val.segments [] rfl
    (MW.leadingChain (RSK.residual m)).val.segments [] rfl rfl
    (List.range (RSK.maxDepth m + 1)) (List.nodup_range)
    (fun c hc hcm => List.mem_range.mpr
      (Nat.lt_succ_of_le (RSK.depth_le_maxDepth m c hcm)))
    (fun d hd c hc => absurd hc (List.not_mem_nil))
  -- the head of the chain carries no specials
  have hJ0 : ((MW.leadingChain m).val.segments.head?.elim 0 (fun σ =>
      if hm : σ ∈ m.segments then
        (if w.1 = σ.a ∧ w.2 < σ.b
         then (((bucket m (depth_of_segment m σ hm)).map (·.val)).map segPair).count w
         else 0)
      else 0)) = 0 := by
    rw [MW.leadingChain_head m sₘ hsₘ]
    simp only [Option.elim]
    by_cases hsm : sₘ ∈ m.segments
    · rw [dif_pos hsm]
      by_cases hcond : w.1 = sₘ.a ∧ w.2 < sₘ.b
      · rw [if_pos hcond]
        rw [List.count_eq_zero]
        intro hmem
        obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hmem
        obtain ⟨hym, -⟩ := RSK.mem_bucket_depth m _ y hy
        have h1 : y.a = w.1 := by rw [← hfy]; rfl
        have h2 : y.b = w.2 := by rw [← hfy]; rfl
        exact no_special_head m sₘ hsₘ y hym (by omega) (by omega)
      · rw [if_neg hcond]
    · rw [dif_neg hsm]
  rw [hJ0] at hres
  omega

/-! ## The `(m′)†` side and the commutation core -/

/-- A sum of equality indicators is a count. -/
lemma sum_ind_eq_count : ∀ (l : List Segment) (x : Segment),
    (l.map (fun c => if x = c then 1 else 0)).sum = l.count x := by
  intro l
  induction l with
  | nil => intro x; simp
  | cons c cs ih =>
    intro x
    rw [List.map_cons, List.sum_cons, count_seg_cons, ih]
    omega

/-- In a duplicate-free list, counts are membership indicators. -/
lemma count_eq_ite_of_nodup (l : List Segment) (hnd : l.Nodup) (x : Segment) :
    l.count x = if x ∈ l then 1 else 0 := by
  by_cases h : x ∈ l
  · rw [if_pos h]
    exact List.count_eq_one_of_mem hnd h
  · rw [if_neg h, List.count_eq_zero]
    exact h

/-- With strictly increasing begins, at most one starred indicator fires. -/
lemma sum_starred_ind : ∀ (l : List Segment),
    l.Pairwise (fun s t => s.a < t.a) → (∀ c ∈ l, c.a < c.b) → ∀ (x : Segment),
    (l.map (fun c => if x.a = c.a + 1 ∧ x.b = c.b then 1 else 0)).sum
      = if ∃ c ∈ l, c.a < c.b ∧ x.a = c.a + 1 ∧ x.b = c.b then 1 else 0 := by
  intro l
  induction l with
  | nil => intro _ _ x; simp
  | cons c cs ih =>
    intro hp hnd x
    obtain ⟨hlt, hp'⟩ := List.pairwise_cons.mp hp
    rw [List.map_cons, List.sum_cons,
      ih hp' (fun c' hc' => hnd c' (List.mem_cons_of_mem _ hc')) x]
    by_cases hc : x.a = c.a + 1 ∧ x.b = c.b
    · have hno : ¬ ∃ c' ∈ cs, c'.a < c'.b ∧ x.a = c'.a + 1 ∧ x.b = c'.b := by
        rintro ⟨c', hc', -, ha, -⟩
        have := hlt c' hc'
        omega
      have hPos : ∃ c' ∈ c :: cs, c'.a < c'.b ∧ x.a = c'.a + 1 ∧ x.b = c'.b :=
        ⟨c, List.mem_cons_self, hnd c List.mem_cons_self, hc.1, hc.2⟩
      rw [if_pos hc, if_neg hno, if_pos hPos]
    · rw [if_neg hc]
      have hiff : (∃ c' ∈ c :: cs, c'.a < c'.b ∧ x.a = c'.a + 1 ∧ x.b = c'.b) ↔
          (∃ c' ∈ cs, c'.a < c'.b ∧ x.a = c'.a + 1 ∧ x.b = c'.b) := by
        constructor
        · rintro ⟨c', hc', h1, h2, h3⟩
          rcases List.mem_cons.mp hc' with rfl | hr
          · exact absurd ⟨h2, h3⟩ hc
          · exact ⟨c', hr, h1, h2, h3⟩
        · rintro ⟨c', hc', h1, h2, h3⟩
          exact ⟨c', List.mem_cons_of_mem _ hc', h1, h2, h3⟩
      by_cases hQ : ∃ c' ∈ cs, c'.a < c'.b ∧ x.a = c'.a + 1 ∧ x.b = c'.b
      · rw [if_pos hQ, if_pos (hiff.mpr hQ)]
      · rw [if_neg hQ, if_neg (fun h => hQ (hiff.mp h))]

/-- Every residual leading-chain entry is nondegenerate. -/
lemma residual_chain_nondegenerate (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a)
    (c : Segment) (hc : c ∈ (MW.leadingChain (RSK.residual m)).val.segments) :
    c.a < c.b := by
  obtain ⟨j, hj, hgetc⟩ := List.getElem_of_mem hc
  have hget? : (MW.leadingChain (RSK.residual m)).val.segments[j]? = some c := by
    rw [List.getElem?_eq_getElem hj, hgetc]
  have hlen := chainLenPreserved m sₘ s_l hsₘ hs_l hmin
  have hjC : j < (MW.leadingChain m).val.segments.length := by omega
  have hσget : (MW.leadingChain m).val.segments[j]? =
      some ((MW.leadingChain m).val.segments[j]'hjC) := List.getElem?_eq_getElem hjC
  obtain ⟨hσm, i, t, l₁, l₂, hbsplit, hia, hta, w', hw'get, hw'a, hw'b⟩ :=
    leadingChain_residual_entries m sₘ s_l hsₘ hs_l hmin j _ hσget
  rw [hget?] at hw'get
  obtain rfl := Option.some.inj hw'get
  have htb : t.a ≤ t.b := t.fst_le_snd
  omega

/-- **The `(m′)†` count identity**: the MW residual of `m′` removes each chain value
and adds its left-shortened copy. -/
lemma count_mdag_residual_pairs (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a)
    (w : ℤ × ℤ) :
    ((MW.makeResidual (RSK.residual m)
        (MW.leadingChain (RSK.residual m)).val.segments).segments.map segPair).count w
      + ((MW.leadingChain (RSK.residual m)).val.segments.map
          (fun c => if w = segPair c then 1 else 0)).sum
    = ((RSK.residual m).segments.map segPair).count w
      + ((MW.leadingChain (RSK.residual m)).val.segments.map
          (fun c => if w = ((c.a + 1 : ℤ), (c.b : ℤ)) then 1 else 0)).sum := by
  classical
  have hBlt' := leadingChain_begins_lt (RSK.residual m)
  have hne' : (MW.leadingChain (RSK.residual m)).val.segments.Pairwise (· ≠ ·) :=
    hBlt'.imp (fun h heq => by rw [heq] at h; omega)
  have hnd' : (MW.leadingChain (RSK.residual m)).val.segments.Nodup := hne'
  have hnondeg := fun c hc =>
    residual_chain_nondegenerate m sₘ s_l hsₘ hs_l hmin c hc
  by_cases hwf : w.1 ≤ w.2
  · set x : Segment := ⟨⟨w.1, w.2⟩, hwf⟩ with hxdef
    have hxw : segPair x = w := rfl
    -- segment-level counts
    have hcm := count_makeResidual (RSK.residual m)
      (MW.leadingChain (RSK.residual m)).val.segments x
    have hce := count_foldl_erase (MW.leadingChain (RSK.residual m)).val.segments
      (RSK.residual m).segments hne'
      (fun c hc => MW.leadingChain_subset _ c hc) x
    have hcf := count_filterMap_residual
      (MW.leadingChain (RSK.residual m)).val.segments hBlt' x
    -- indicator sums as counts
    have hs1 : ((MW.leadingChain (RSK.residual m)).val.segments.map
        (fun c => if w = segPair c then 1 else 0)).sum
        = if x ∈ (MW.leadingChain (RSK.residual m)).val.segments then 1 else 0 := by
      rw [← count_eq_ite_of_nodup _ hnd' x, ← sum_ind_eq_count]
      refine congrArg List.sum (List.map_congr_left ?_)
      intro c _
      by_cases h : x = c
      · rw [if_pos h, if_pos (by rw [← h, hxw])]
      · rw [if_neg h, if_neg (fun hh => h (segPair_inj (by rw [hxw, hh])))]
    have hs3 : ((MW.leadingChain (RSK.residual m)).val.segments.map
        (fun c => if w = ((c.a + 1 : ℤ), (c.b : ℤ)) then 1 else 0)).sum
        = if ∃ c ∈ (MW.leadingChain (RSK.residual m)).val.segments,
            c.a < c.b ∧ x.a = c.a + 1 ∧ x.b = c.b then 1 else 0 := by
      rw [← sum_starred_ind _ hBlt' hnondeg x]
      refine congrArg List.sum (List.map_congr_left ?_)
      intro c _
      by_cases h : x.a = c.a + 1 ∧ x.b = c.b
      · rw [if_pos (by rw [pair_eq_iff]; exact ⟨h.1, h.2⟩), if_pos h]
      · rw [if_neg (fun hh => h (by rw [pair_eq_iff] at hh; exact ⟨hh.1, hh.2⟩)),
          if_neg h]
    have hc1 : ((MW.makeResidual (RSK.residual m)
        (MW.leadingChain (RSK.residual m)).val.segments).segments.map segPair).count w
        = (MW.makeResidual (RSK.residual m)
          (MW.leadingChain (RSK.residual m)).val.segments).segments.count x := by
      rw [← hxw, count_map_segPair_eq]
    have hc2 : ((RSK.residual m).segments.map segPair).count w
        = (RSK.residual m).segments.count x := by
      rw [← hxw, count_map_segPair_eq]
    rw [hc1, hc2, hs1, hs3]
    omega
  · push_neg at hwf
    have hz1 : ((MW.leadingChain (RSK.residual m)).val.segments.map
        (fun c => if w = segPair c then 1 else 0)).sum = 0 := by
      rw [List.map_congr_left (g := fun _ => (0 : ℕ)) ?_]
      · simp
      · intro c hc
        rw [if_neg]
        intro h
        have h1 : w.1 = c.a := by rw [h]; rfl
        have h2 : w.2 = c.b := by rw [h]; rfl
        have h3 : c.a ≤ c.b := c.fst_le_snd
        omega
    have hz2 : ((MW.leadingChain (RSK.residual m)).val.segments.map
        (fun c => if w = ((c.a + 1 : ℤ), (c.b : ℤ)) then 1 else 0)).sum = 0 := by
      rw [List.map_congr_left (g := fun _ => (0 : ℕ)) ?_]
      · simp
      · intro c hc
        rw [if_neg]
        intro h
        have h1 : w.1 = c.a + 1 := by rw [h]
        have h2 : w.2 = c.b := by rw [h]
        have h3 := hnondeg c hc
        omega
    rw [count_map_segPair_illformed _ w hwf, count_map_segPair_illformed _ w hwf,
      hz1, hz2]

/-- Multisegments with equal segment lists are equal. -/
lemma Multisegment.eq_of_segments_eq {A B : Multisegment}
    (h : A.segments = B.segments) : A = B := by
  cases A with | mk s hs =>
  cases B with | mk s' hs' =>
  simp only at h
  subst h
  rfl

/-- **The commutation core** (paper Cor. `main`, third component): applying MW then RSK
equals applying RSK then MW, at the level of segment lists. -/
lemma residual_commute_core (m : Multisegment) (sₘ s_l : Segment)
    (hsₘ : m.segments.head? = some sₘ)
    (hs_l : (RSK.ladderRungs m).head? = some s_l) (hmin : sₘ.a < s_l.a) :
    (RSK.residual (MW.makeResidual m (MW.leadingChain m).val.segments)).segments
      = (MW.makeResidual (RSK.residual m)
          (MW.leadingChain (RSK.residual m)).val.segments).segments := by
  classical
  have hm : m.segments ≠ [] := by
    intro h
    rw [h] at hsₘ
    simp at hsₘ
  -- m† is nonempty: it contains the starred head
  have hsₘC : sₘ ∈ (MW.leadingChain m).val.segments := by
    have h := MW.leadingChain_head m sₘ hsₘ
    rw [head?_eq_cons h]
    exact List.mem_cons_self
  have hndg : sₘ.a < sₘ.b := chain_seg_nondegenerate m sₘ s_l hsₘ hs_l hmin sₘ hsₘC
  have hmdne : (MW.makeResidual m (MW.leadingChain m).val.segments).segments ≠ [] :=
    List.ne_nil_of_mem (starred_mem_mdag m _ sₘ hsₘC hndg)
  have hmaxeq := mdag_maxDepth_eq m sₘ s_l hsₘ hs_l hmin hm hmdne
  -- coordinate counts agree everywhere
  have hkey : ∀ w : ℤ × ℤ,
      ((RSK.residual (MW.makeResidual m
        (MW.leadingChain m).val.segments)).segments.map segPair).count w
      = ((MW.makeResidual (RSK.residual m)
          (MW.leadingChain (RSK.residual m)).val.segments).segments.map segPair).count w := by
    intro w
    have h1 := residual_count_telescope m sₘ s_l hsₘ hs_l hmin w
    have h2 := count_mdag_residual_pairs m sₘ s_l hsₘ hs_l hmin w
    have h3 := count_residual_pairs (MW.makeResidual m
      (MW.leadingChain m).val.segments) w
    have h4 := count_residual_pairs m w
    rw [hmaxeq] at h3
    omega
  -- segment counts agree everywhere
  have hcnt : ∀ x : Segment,
      (RSK.residual (MW.makeResidual m
        (MW.leadingChain m).val.segments)).segments.count x
      = (MW.makeResidual (RSK.residual m)
          (MW.leadingChain (RSK.residual m)).val.segments).segments.count x := by
    intro x
    have h := hkey (segPair x)
    rw [count_map_segPair_eq, count_map_segPair_eq] at h
    exact h
  refine (List.perm_iff_count.mpr hcnt).eq_of_pairwise ?_
    (RSK.residual _).is_sorted
    (MW.makeResidual (RSK.residual m) _).is_sorted
  intro a b _ _ h1 h2
  exact le_antisymm h1 h2
