import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.Ladder1_t
import LeanProof.Ladder1_u
import LeanProof.Ladder2_t
import LeanProof.Ladder2_u
import LeanProof.RSK1_t
import LeanProof.RSK1_u
import LeanProof.RSK2_t
import LeanProof.RSK2_u
import Mathlib.Data.List.Sort

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.hashCommand false

namespace RSK

/-! # RSK algorithm — single step (trusted definitions)

One step of the RSK / MW algorithm: given a multisegment `m`, produce the
maximal ladder rungs and the residual multisegment.

Each bucket's rung is the coordinatewise max of its segments (`bucketRung`);
`ladderRungs` is the set of them. The residual replaces each neighbouring pair
`Δᵢ, Δᵢ₊₁` of a fiber by the derived segment `[Δᵢ.a, Δᵢ₊₁.b]`. The correctness
lemmas (`ladderRungs_isLadder`, Lemma 2.2, Corollary 2.3) live in `RSK3_u`. -/

/-- `d(m) = max_{i ∈ I} 𝔡(i)`, the depth of a nonzero multisegment. -/
def maxDepth (m : Multisegment) (h : m.segments ≠ []) : ℕ :=
  maximum [depth_of_segment m s | s ∈ m.segments]

/-- `𝔩(m)`: the rungs of all fibers. -/
def ladderRungs (m : Multisegment) : Set Segment :=
  { r | ∃ k, bucketRung m k = some r }

/-- Paper (2.1a): `Δ'_i = [b(Δ_i), e(Δ_{i^∨})]` where `Δ_{i^∨} = Δ_{i+1}` is
the next segment of the fiber `𝔡⁻¹(d)` (in the order of our enumeration). -/
def bucketResidual (m : Multisegment) (d : ℕ) : List Segment :=
  [Segment (fiber m d)[i].a (fiber m d)[i + 1].b | i < (fiber m d).length - 1]

-- /-- `i^\vee`: the nesting successor of `s` in bucket `d` (the next, more-inner segment in
-- admissible order); `none` if `s` is the innermost element. -/
-- def bucketSucc (m : Multisegment) (d : ℕ) (s : Segment) : Option Segment :=
--   let l := (bucket m d).map (·.val)
--   ((l.zip l.tail).find? (fun p => decide (p.1 = s))).map (·.2)

/-- `m′ = Σ_{i ∈ I′′} Δ'_i` (paper (2.1c)): all the derived segments, of all fibers. -/
def residual (m : Multisegment) (h : m.segments ≠ []) : Multisegment :=
  [s | k ≤ maxDepth m, s ∈ bucketResidual m k]

/-- **One step of the RSK algorithm** on a nonzero multisegment: the extracted ladder and
the residual. -/
def rsk_step (m : Multisegment) (h : m.segments ≠ []) : Set Segment × Multisegment :=
  (ladderRungs m, residual m)

end RSK
