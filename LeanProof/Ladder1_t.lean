import LeanProof.Basic_t
import LeanProof.Basic_u
import Mathlib.Data.Set.Defs

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false

/-- `j + 1` indices `i₀, …, iⱼ` into `m`. -/
def Indices (j : ℕ) (m : Multisegment) : Set (List ℕ) :=
  { i | i.length = j + 1 ∧ ∀ k ∈ i, k < m.segments.length }

-- Discharges the index-validity side goals of `m.segments[i.val[r]]` below.
local macro_rules
  | `(tactic| get_elem_tactic_extensible) =>
    `(tactic| grind [Indices, List.getElem_mem])

/-- d(Δ) = max{j : ∃ i₀ = Δ, i₁, …, iⱼ ∈ I such that Δ_{iᵣ} ≪ Δ_{iᵣ₊₁}, r = 0, …, j − 1} -/
def depthSet (m : Multisegment) (s : Segment) : Set ℕ :=
  { j | ∃ i : Indices j m,
        m.segments[i.val[0]] = s ∧
        ∀ r (_ : r < j), m.segments[i.val[r]] ≪ m.segments[i.val[r + 1]] }
