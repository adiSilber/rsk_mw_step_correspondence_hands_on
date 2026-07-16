import LeanProof.Propositions_t
import LeanProof.Propositions_u

/-- **Δ°(m) = Δ°(m′)** (paper Prop. `lem: main2`(2)): under `min m < min L(m)`, one MW
step on `m` and on its RSK residual produce the same segment. Assembled from
`minPreserved` (the head begins agree) and `chainLenPreserved` (the leading-chain
lengths agree). -/
lemma deltaCirc_eq_of_residual
    (m : Multisegment) (hm : m.segments ≠ []) (h_min : min_m_lt_min_lm m hm) :
    let Δ : Segment := (MW.mw_step m hm).1
    let Δ' : Segment := (MW.mw_step (RSK.residual m) (cond_rsk_residual_nonempty m hm h_min)).1
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
