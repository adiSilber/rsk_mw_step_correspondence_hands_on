import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.Ladder1_t
import LeanProof.Ladder1_u
import LeanProof.Ladder2_t
import LeanProof.Ladder2_u
import LeanProof.RSK1_t
import LeanProof.RSK1_u

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false

/-! # RSK, part 2: the rung of a fiber (trusted definitions) -/

/-- The rung of a nonempty fiber `𝔡⁻¹(d)` (paper (2.2)): the largest begin point paired with
the largest end point. -/
def bucketRung (m : Multisegment) (d : ℕ) (h : fiber m d ≠ []) : Segment :=
  Segment (maximum {(x.a) | x ∈ fiber m d}) (maximum {(x.b) | x ∈ fiber m d})
