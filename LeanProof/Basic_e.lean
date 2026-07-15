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
