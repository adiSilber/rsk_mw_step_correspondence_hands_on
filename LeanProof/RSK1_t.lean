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

/-! # RSK, part 1: our choice of admissible enumerations (trusted definitions)

Paper, §2: "For any `k = 0, …, d` choose an admissible enumeration of `𝔡⁻¹(k)`". -/

/-- Our admissible enumeration `i^k_0, …, i^k_{l-1}` of `𝔡⁻¹(k)`: the first one. -/
def enumeration (m : Multisegment) (k : ℕ) : List ℕ :=
  first (admissibleEnumerations m k)

end RSK
