import LeanProof.Lemmas_u

seal maximum first in
/-- **Corollary 3.4** (paper Cor. `main`): `(K × Id)(MW(m)) = (Id × MW)(K(m))` for
`min m < min L(m)` — one MW step followed by one RSK step yields the same data as one
RSK step followed by one MW step. Both sides are the triple
(extracted ladder, remaining multisegment, MW segment):
* left — `MW` first: the ladder and remainder of `m†`, with `Δ°(m)`;
* right — `K` first: the ladder of `m`, with the MW step of `m′`.
Assembled from `mw_preserves_ladder`, `mw_residual_commute` and
`deltaCirc_eq_of_residual` (`Lemmas_u`). -/
theorem corollary_3_4
    (m : Multisegment) (hm : m.segments ≠ [])
    (h_min : (m.segments.head hm).a < ((sorted (ladderRungs m)).head).a) :
    let KId_MW : Set Segment × Multisegment × Segment :=
      ((rsk_step (mw_step m hm).2).1,
       (rsk_step (mw_step m hm).2).2,
       (mw_step m hm).1)
    let IdMW_K : Set Segment × Multisegment × Segment :=
      ((rsk_step m).1,
       (mw_step (rsk_step m).2 (cond_rsk_residual_nonempty m hm h_min)).2,
       (mw_step (rsk_step m).2 (cond_rsk_residual_nonempty m hm h_min)).1)
    KId_MW = IdMW_K := by
  intro KId_MW IdMW_K
  have h1 : (rsk_step m).1 = (rsk_step (mw_step m hm).2).1 :=
    mw_preserves_ladder m hm h_min
  have h2 : (rsk_step (mw_step m hm).2).2
      = (mw_step (rsk_step m).2 (cond_rsk_residual_nonempty m hm h_min)).2 :=
    mw_residual_commute m hm h_min
  have h3 : (mw_step m hm).1
      = (mw_step (rsk_step m).2 (cond_rsk_residual_nonempty m hm h_min)).1 :=
    deltaCirc_eq_of_residual m hm h_min
  exact congrArg₂ Prod.mk h1.symm (congrArg₂ Prod.mk h2 h3)
