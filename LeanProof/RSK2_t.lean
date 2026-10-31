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

/-- The rung of `𝔡⁻¹(d)` (paper (2.2)): the largest begin point paired with the largest end
point; `none` if the fiber is empty. -/
def bucketRung (m : Multisegment) (d : ℕ) : Option Segment :=
  match fiber m d with
  | []      => none
  | s :: ss => some (Segment (maximum {(x.a) | x ∈ s :: ss}) (maximum {(x.b) | x ∈ s :: ss}))
