import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.MW1_t
import LeanProof.MW1_u
import LeanProof.MW2_t

set_option linter.style.setOption false
set_option autoProp.rule false
set_option linter.flexible false
set_option linter.style.whitespace false

/-!
# Mœglin–Waldspurger, part 2: proofs

The step in terms of the greedy chain of `MW1_u`: the leading chain is it (`leadingChain_eq`),
the residual is the computation along it (`mw_step_snd_eq`), and `Δ^MW(m)` is
`[min m, min m + k − 1]` (`mw_step_fst_a`, `mw_step_fst_b`). This is what the propositions
reason about.
-/

lemma leadingChain_eq (m : Multisegment) (hm : m.segments ≠ []) :
    leadingChain m hm = (Proof.greedyChain m).val.segments := by
  unfold leadingChain
  rw [anyOf_eq (first_mem _ (leadingIndices_nonempty m hm))]
  exact segments_of_leadingIndices m (first_mem _ _)

lemma makeResidual_eq (m : Multisegment) (hm : m.segments ≠ []) :
    makeResidual m hm = Proof.residualAlong m (Proof.greedyChain m).val.segments := by
  unfold makeResidual
  have hi := first_mem _ (leadingIndices_nonempty m hm)
  rw [anyOf_eq hi]
  exact residual_eq m hi

lemma deltaCirc_a (m : Multisegment) (hm : m.segments ≠ []) :
    (deltaCirc m hm).a = (m.segments.head hm).a := by
  unfold deltaCirc
  have hi := first_mem _ (leadingIndices_nonempty m hm)
  rw [anyOf_eq hi]
  change m.segments[(first (leadingIndices m) _)[0]].a = _
  rw [getElem_zero_eq_head hm hi]

lemma deltaCirc_b (m : Multisegment) (hm : m.segments ≠ []) :
    (deltaCirc m hm).b
      = (m.segments.head hm).a + ↑((Proof.greedyChain m).val.segments.length - 1) := by
  unfold deltaCirc
  have hi := first_mem _ (leadingIndices_nonempty m hm)
  rw [anyOf_eq hi]
  exact a_last_eq hm hi

lemma mw_step_fst_a (m : Multisegment) (hm : m.segments ≠ []) :
    (mw_step m hm).1.a = (m.segments.head hm).a := deltaCirc_a m hm

lemma mw_step_fst_b (m : Multisegment) (hm : m.segments ≠ []) :
    (mw_step m hm).1.b
      = (m.segments.head hm).a + ↑((Proof.greedyChain m).val.segments.length - 1) :=
  deltaCirc_b m hm

/-- The MW residual of `mw_step` is the residual along the greedy chain. -/
lemma mw_step_snd_eq (m : Multisegment) (hm : m.segments ≠ []) :
    (mw_step m hm).2 = Proof.residualAlong m (Proof.greedyChain m).val.segments :=
  makeResidual_eq m hm
