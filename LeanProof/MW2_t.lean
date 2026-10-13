import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.MW1_t
import LeanProof.MW1_u
import Mathlib.Data.List.Sort

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false

/-!
# Mœglin–Waldspurger, part 2: one step `MW(m) = (Δ°(m), m^MW)` (trusted definitions)
-/

namespace MW

def leadingChain (m : Multisegment) (h : m.segments ≠ []) : List Segment :=
  [m.segments[i] | i ∈ first (leadingIndices m)]

/-- Residual of a chain segment: `[a, b] → [a+1, b]`; singletons are discarded. -/
def segmentResidual (s : Segment) : Option Segment :=
  if h : s.a < s.b then some ⟨⟨s.a + 1, s.b⟩, by omega⟩ else none

/-- Remove chain segments from `m`, add back their residuals, then re-sort. -/
def makeResidual (m : Multisegment) (chain : List Segment) : Multisegment :=
  let m_without := chain.foldl List.erase m.segments
  let residuals := chain.filterMap segmentResidual
  ⟨(m_without ++ residuals).insertionSort (· ≤ ·), List.pairwise_insertionSort _ _⟩

def mw_step (m : Multisegment) (h : m.segments ≠ []) : Segment × Multisegment :=
  let s_min := m.segments.head h
  let chain := leadingChain m h
  let k := chain.length
  let delta_circ := ⟨⟨s_min.a, s_min.a + ↑(k - 1)⟩, by omega⟩
  let residual := makeResidual m chain
  (delta_circ, residual)

end MW
