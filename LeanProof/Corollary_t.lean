import LeanProof.Propositions_t
import LeanProof.Propositions_u

/-- **Δ°(m) = Δ°(m′)** (paper Prop. `lem: main2`(2)): under `min m < min L(m)`, the MW
segment of `m` equals the MW segment of its RSK residual `(rsk_step m).2`. Assembled
from `minPreserved` (the head begins agree) and `chainLenPreserved` (the leading-chain
lengths agree). -/
lemma deltaCirc_eq_of_residual
    (m : Multisegment) (hm : m.segments ≠ []) (h_min : min_m_lt_min_lm m hm) :
    let Δ : Segment := (MW.mw_step m hm).1
    let Δ' : Segment :=
      (MW.mw_step (RSK.rsk_step m).2 (cond_rsk_residual_nonempty m hm h_min)).1
    Δ = Δ' := by
  intro Δ Δ'
  have hne' := cond_rsk_residual_nonempty m hm h_min
  have hsₘ : m.segments.head? = some (m.segments.head hm) := List.head?_eq_some_head hm
  have hs_l : (RSK.ladderRungs m).head? =
      some ((RSK.ladderRungs m).head (RSK.ladderRungs_ne_nil m hm)) :=
    List.head?_eq_some_head _
  have hmin : (m.segments.head hm).a
      < ((RSK.ladderRungs m).head (RSK.ladderRungs_ne_nil m hm)).a := h_min
  have hs_m' : (RSK.residual m).segments.head? =
      some ((RSK.residual m).segments.head hne') := List.head?_eq_some_head hne'
  apply mw_step_fst_eq m (RSK.residual m) hm hne'
  · exact minPreserved m _ hsₘ _ hs_l hmin _ hs_m'
  · exact chainLenPreserved m _ _ hsₘ hs_l hmin

/-- **L(m) = L(m†)** (paper Prop. `main2`(3) via Lemma `pre1`): under `min m < min L(m)`,
the RSK ladder survives one MW step unchanged. The depth function of the MW residual
agrees with `m`'s except on *special* segments, which move up by exactly one level into
the fiber of the chain predecessor — and neither coordinatewise fiber max is disturbed. -/
lemma mw_preserves_ladder
    (m : Multisegment) (hm : m.segments ≠ []) (h_min : min_m_lt_min_lm m hm) :
    let l := (RSK.rsk_step m).1
    let l' := (RSK.rsk_step (MW.mw_step m hm).2).1
    l = l' := by
  intro l l'
  have hsₘ : m.segments.head? = some (m.segments.head hm) := List.head?_eq_some_head hm
  have hs_l : (RSK.ladderRungs m).head? =
      some ((RSK.ladderRungs m).head (RSK.ladderRungs_ne_nil m hm)) :=
    List.head?_eq_some_head _
  have hmin : (m.segments.head hm).a
      < ((RSK.ladderRungs m).head (RSK.ladderRungs_ne_nil m hm)).a := h_min
  have h := (mdag_ladder_eq m _ _ hsₘ hs_l hmin hm).symm
  rw [← mw_step_snd_eq m hm] at h
  exact h

/-- **(m†)′ = (m′)†** (paper Cor. `main`, third component): under `min m < min L(m)`,
the two orders of taking the remainders agree —
`m'`  is MW-step first, then the RSK step;
`m''` is the RSK step first, then MW-step. -/
lemma mw_residual_commute
    (m : Multisegment) (hm : m.segments ≠ []) (h_min : min_m_lt_min_lm m hm) :
    let m' : Multisegment := (RSK.rsk_step (MW.mw_step m hm).2).2
    let m'' : Multisegment :=
      (MW.mw_step (RSK.rsk_step m).2 (cond_rsk_residual_nonempty m hm h_min)).2
    m' = m'' := by
  intro m' m''
  have hne' := cond_rsk_residual_nonempty m hm h_min
  have hsₘ : m.segments.head? = some (m.segments.head hm) := List.head?_eq_some_head hm
  have hs_l : (RSK.ladderRungs m).head? =
      some ((RSK.ladderRungs m).head (RSK.ladderRungs_ne_nil m hm)) :=
    List.head?_eq_some_head _
  have hmin : (m.segments.head hm).a
      < ((RSK.ladderRungs m).head (RSK.ladderRungs_ne_nil m hm)).a := h_min
  have h1 : (RSK.rsk_step (MW.mw_step m hm).2).2
      = RSK.residual (MW.makeResidual m (MW.leadingChain m).val.segments) := by
    rw [mw_step_snd_eq m hm]
    rfl
  have h2 : (MW.mw_step (RSK.rsk_step m).2 hne').2
      = MW.makeResidual (RSK.residual m)
          (MW.leadingChain (RSK.residual m)).val.segments :=
    mw_step_snd_eq (RSK.residual m) hne'
  exact h1.trans ((Multisegment.eq_of_segments_eq
    (residual_commute_core m _ _ hsₘ hs_l hmin)).trans h2.symm)
