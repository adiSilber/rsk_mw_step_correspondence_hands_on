import LeanProof.Basic_t
import LeanProof.Ladder1_t
-- For the `Decidable` / `Fintype` instances that make `Indices` and `depthSet` evaluable.
import LeanProof.Ladder1_u
import Mathlib.Data.Finset.Sort

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.hashCommand false

-- m = [(1,3), (1,4), (2,5)] — sorted lex; (1,3) and (1,4) share an `a`
def m_tie : Multisegment :=
  ⟨[⟨⟨1, 3⟩, by omega⟩, ⟨⟨1, 4⟩, by omega⟩, ⟨⟨2, 5⟩, by omega⟩], by decide⟩

/-! ### `Indices` -/

-- [0, 2] — length 2 = 1 + 1, entries < 3 — true
#eval decide ([0, 2] ∈ Indices 1 m_tie)
-- [0, 2] has length 2, not 0 + 1 — false
#eval decide ([0, 2] ∈ Indices 0 m_tie)
-- [0, 3] — index 3 is out of range — false
#eval decide ([0, 3] ∈ Indices 1 m_tie)
-- [1, 1] — repeated indices are allowed by `Indices` — true
#eval decide ([1, 1] ∈ Indices 1 m_tie)
-- empty multisegment: no index is valid — false
#eval decide ([0] ∈ Indices 0 ⟨[], by decide⟩)

/-! ### `depthSet` (shown via its computed `toFinset`) -/

-- (1,3): j = 0 via [(1,3)], j = 1 via (1,3) ≪ (2,5) — [0, 1]
#eval (depthSet m_tie ⟨⟨1, 3⟩, by omega⟩).toFinset.sort (· ≤ ·)
-- (1,4): j = 1 via (1,4) ≪ (2,5) — [0, 1]
#eval (depthSet m_tie ⟨⟨1, 4⟩, by omega⟩).toFinset.sort (· ≤ ·)
-- (2,5): nothing above it — [0]
#eval (depthSet m_tie ⟨⟨2, 5⟩, by omega⟩).toFinset.sort (· ≤ ·)
-- (7,9) is not in m — []
#eval (depthSet m_tie ⟨⟨7, 9⟩, by omega⟩).toFinset.sort (· ≤ ·)
-- m = [(1,3), (2,4), (3,5)], a ladder: from (1,3) — [0, 1, 2]
#eval (depthSet ⟨[⟨⟨1, 3⟩, by omega⟩, ⟨⟨2, 4⟩, by omega⟩, ⟨⟨3, 5⟩, by omega⟩], by decide⟩
  ⟨⟨1, 3⟩, by omega⟩).toFinset.sort (· ≤ ·)
-- repeated segment m = [(1,3), (1,3)]: (1,3) ≪ (1,3) fails — [0]
#eval (depthSet ⟨[⟨⟨1, 3⟩, by omega⟩, ⟨⟨1, 3⟩, by omega⟩], by decide⟩
  ⟨⟨1, 3⟩, by omega⟩).toFinset.sort (· ≤ ·)
-- singleton segment (4,4) in m = [(4,4)] — [0]
#eval (depthSet ⟨[⟨⟨4, 4⟩, by omega⟩], by decide⟩ ⟨⟨4, 4⟩, by omega⟩).toFinset.sort (· ≤ ·)
-- empty multisegment — []
#eval (depthSet ⟨[], by decide⟩ ⟨⟨1, 3⟩, by omega⟩).toFinset.sort (· ≤ ·)
