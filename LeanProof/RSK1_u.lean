import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.Ladder1_t
import LeanProof.Ladder1_u
import LeanProof.Ladder2_t
import LeanProof.Ladder2_u
import LeanProof.RSK1_t

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false

namespace RSK

/-! # RSK, part 1: proofs

Our enumeration is an admissible enumeration whenever the fiber is nonempty
(`enumeration_mem`), and its entries are valid indices of `m`
(`lt_length_of_mem_enumeration`), which lets `RSK2_t` write `m.segments[i]`. -/

lemma enumeration_mem (m : Multisegment) (k : ℕ) :
    enumeration m k ∈ admissibleEnumerations m k :=
  first_mem _ _

lemma enumeration_eq_nil {m : Multisegment} {k : ℕ}
    (h : ∀ j : Fin m.segments.length, depth_of_segment m m.segments[j] ≠ k) :
    enumeration m k = [] :=
  eq_nil_of_mem_admissibleEnumerations h (enumeration_mem m k)

/-- The entries of our enumeration are valid indices of `m`. -/
lemma lt_length_of_mem_enumeration {m : Multisegment} {k i : ℕ}
    (hi : i ∈ enumeration m k) : i < m.segments.length :=
  lt_length_of_mem_admissibleEnumerations (enumeration_mem m k) i hi

end RSK

-- The index rule learns it: `m.segments[i]` is valid for `i ∈ RSK.enumeration m k`.
macro_rules
  | `(tactic| get_elem_tactic_extensible) =>
    `(tactic| (apply RSK.lt_length_of_mem_enumeration; assumption))
