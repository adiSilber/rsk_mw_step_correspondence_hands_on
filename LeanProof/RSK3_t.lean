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
`ladderRungs` assembles them deepest-first. The residual replaces each
consecutive nested pair `(s, t)` of a bucket by the derived segment
`[s.a, t.b]`. The correctness lemmas (`ladderRungs_isLadder`, Lemma 2.2,
Corollary 2.3) and the `Ladder`-packaged step `rskStep` live in `RSK3_u`. -/

/-- `d(m) = max_{i ∈ I} 𝔡(i)`, the depth of a nonzero multisegment. -/
def maxDepth (m : Multisegment) (h : m.segments ≠ []) : ℕ :=
  maximum [depth_of_segment m s | s ∈ m.segments]

/-- `𝔩(m)`: the rungs of all fibers, in increasing order (= deepest first). -/
def ladderRungs (m : Multisegment) : List Segment :=
  sorted { r | ∃ k, bucketRung m k = some r }

/-- Residual of `𝔡⁻¹(d)` (paper (2.1a)): consecutive segments `Δ_{i_r} ⊇ Δ_{i_{r+1}}` of our
enumeration give `[b(Δ_{i_r}), e(Δ_{i_{r+1}})]`. -/
def bucketResidual (m : Multisegment) (d : ℕ) : List Segment :=
  [Segment p.1.a p.2.b | p ∈ (fiber m d).zip (fiber m d).tail]

-- /-- `i^\vee`: the nesting successor of `s` in bucket `d` (the next, more-inner segment in
-- admissible order); `none` if `s` is the innermost element. -/
-- def bucketSucc (m : Multisegment) (d : ℕ) (s : Segment) : Option Segment :=
--   let l := (bucket m d).map (·.val)
--   ((l.zip l.tail).find? (fun p => decide (p.1 = s))).map (·.2)

/-- The changed (residual) multisegment: every bucket's residual, re-sorted. -/
def residual (m : Multisegment) (h : m.segments ≠ []) : Multisegment :=
  let raw := (List.range (maxDepth m + 1)).flatMap (fun d => bucketResidual m d)
  ⟨raw.insertionSort (· ≤ ·), List.pairwise_insertionSort _ _⟩

/-- **One step of the RSK algorithm** on a nonzero multisegment: the extracted ladder and
the residual. -/
def rsk_step (m : Multisegment) (h : m.segments ≠ []) : List Segment × Multisegment :=
  (ladderRungs m, residual m)

end RSK
