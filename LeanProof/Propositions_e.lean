import LeanProof.Propositions_t

set_option linter.style.setOption false
set_option linter.hashCommand false

/-! # Evals for the Propositions-level trusted definitions

`min_m_lt_min_lm m h` says the smallest begin of `m` is strictly below the smallest
begin of its extracted ladder `L(m)` — the side condition of Corollary 3.4. -/

instance (m : Multisegment) (h : m.segments ≠ []) : Decidable (min_m_lt_min_lm m h) := by
  unfold min_m_lt_min_lm
  infer_instance

-- m = [(1,10), (2,3)]: both segments share depth 0, the rung is (2,10), so
-- min L(m) = 2 > 1 = min m — true.
#eval decide (min_m_lt_min_lm
  ⟨[⟨⟨1, 10⟩, by omega⟩, ⟨⟨2, 3⟩, by omega⟩], by decide⟩ (by simp))

-- m = [(1,3)] (a single segment): L(m) = [(1,3)], so min L(m) = min m — false
-- (edge case: the condition fails on any singleton).
#eval decide (min_m_lt_min_lm
  ⟨[⟨⟨1, 3⟩, by omega⟩], by simp⟩ (by simp))

-- m = [(1,3), (2,4), (3,5)] (a ladder): the single rung starts at min m — false.
#eval decide (min_m_lt_min_lm
  ⟨[⟨⟨1, 3⟩, by omega⟩, ⟨⟨2, 4⟩, by omega⟩, ⟨⟨3, 5⟩, by omega⟩], by decide⟩ (by simp))
