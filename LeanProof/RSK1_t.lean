import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.Ladder1_t
import LeanProof.Ladder1_u
import LeanProof.Ladder2_t
import LeanProof.Ladder2_u
import Mathlib.Data.List.Lex

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false

namespace RSK

/-! # RSK, part 1: the fibers (trusted definitions)

Paper, §2: "For any `k = 0, …, d` choose an admissible enumeration of `𝔡⁻¹(k)`". -/

/-- `Δ_{i^k_0} ⊇ … ⊇ Δ_{i^k_l}`: the segments of `𝔡⁻¹(k)` in the order of an admissible
enumeration (any one: they all list the same segments). -/
def fiber (m : Multisegment) (k : ℕ) : List Segment :=
  let i ∈ admissibleEnumerations m k; [m.segments[j] | j ∈ i]

end RSK
