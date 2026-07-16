import LeanProof.RSK_t
import LeanProof.RSK_u
import LeanProof.MW_t

def min_m_lt_min_lm (m : Multisegment) (h : m.segments ≠ []) : Prop :=
  (m.segments.head h).a < ((RSK.ladderRungs m).head (RSK.ladderRungs_ne_nil m h)).a

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

lemma deltaCirc_eq_of_residual
    (m : Multisegment) (hm : m.segments ≠ []) (h_min : min_m_lt_min_lm m hm) :
    let Δ : Segment := (MW.mw_step m hm).1
    let Δ' : Segment := (MW.mw_step (RSK.residual m) (cond_rsk_residual_nonempty m hm h_min)).1
    Δ = Δ' := by sorry
