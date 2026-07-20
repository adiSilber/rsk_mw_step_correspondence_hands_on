import LeanProof.Basic_t
import LeanProof.Basic_u
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Sort
-- import Mathlib.Data.Set.Finite


set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.hashCommand false

-- (1,3) ≪ (2,4): 1<2 ∧ 3<4 — true
#eval decide ((⟨⟨1, 3⟩, by omega⟩ : Segment) ≪ ⟨⟨2, 4⟩, by omega⟩)
-- (2,4) ≪ (1,3): false
#eval decide ((⟨⟨2, 4⟩, by omega⟩ : Segment) ≪ ⟨⟨1, 3⟩, by omega⟩)
-- (1,5) ≪ (2,4): a₁<a₂ ok, but b₁=5 > b₂=4 — false
#eval decide ((⟨⟨1, 5⟩, by omega⟩ : Segment) ≪ ⟨⟨2, 4⟩, by omega⟩)

-- (2,3) ⊆ (1,5) — true (contained in [1,5])
#eval decide ((⟨⟨2, 3⟩, by omega⟩ : Segment) ⊆ ⟨⟨1, 5⟩, by omega⟩)
-- (1,5) ⊆ (2,3) — false
#eval decide ((⟨⟨1, 5⟩, by omega⟩ : Segment) ⊆ ⟨⟨2, 3⟩, by omega⟩)
-- (1,3) ⊆ (1,3) — reflexive
#eval decide ((⟨⟨1, 3⟩, by omega⟩ : Segment) ⊆ ⟨⟨1, 3⟩, by omega⟩)

-- Segment coordinates: a (begin) and b (end) of (3,7); edge case: a singleton (5,5).
#eval Segment.a ⟨⟨3, 7⟩, by omega⟩  -- 3
#eval Segment.b ⟨⟨3, 7⟩, by omega⟩  -- 7
#eval Segment.a ⟨⟨5, 5⟩, by omega⟩  -- 5
#eval Segment.b ⟨⟨5, 5⟩, by omega⟩  -- 5

-- Multisegment inclusion `subms` (segment lists as sublists).
-- [(1,3)] ⊆ [(1,3),(2,4)] — true; edge cases: the empty multisegment is ⊆ anything,
-- and inclusion fails when the order is wrong or an element is missing.
#eval decide ((⟨[⟨⟨1, 3⟩, by omega⟩], by simp⟩ : Multisegment)
  ⊆ ⟨[⟨⟨1, 3⟩, by omega⟩, ⟨⟨2, 4⟩, by omega⟩], by decide⟩)  -- true
#eval decide ((⟨[], by simp⟩ : Multisegment)
  ⊆ ⟨[⟨⟨1, 3⟩, by omega⟩], by simp⟩)  -- true (empty ⊆ anything)
#eval decide ((⟨[⟨⟨2, 4⟩, by omega⟩], by simp⟩ : Multisegment)
  ⊆ ⟨[⟨⟨1, 3⟩, by omega⟩], by simp⟩)  -- false
