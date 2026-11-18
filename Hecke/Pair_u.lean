import Hecke.Pair_t

set_option autoProp.rule false

/-! # Functional-equation pairs: proofs

The one fact `Theta1_u` needs about the device: a Mathlib pair's data is valid. -/

noncomputable section

/-- A Mathlib pair's data satisfies the seven facts: Mathlib's own proofs. -/
theorem WeakFEPair.data_valid (P : WeakFEPair ℂ) : P.data.Valid :=
  ⟨P.hf_int, P.hg_int, P.hk, P.hε, P.h_feq, P.hf_top, P.hg_top⟩

end
