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
