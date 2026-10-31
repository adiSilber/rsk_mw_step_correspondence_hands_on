import LeanProof.Basic_t
import LeanProof.RSK3_t
import LeanProof.RSK3_u

set_option linter.style.setOption false
set_option linter.hashCommand false

/-! # Evals for the side condition of Corollary 3.4

`min m < min L(m)`: the smallest begin of `m` is strictly below the smallest begin of its
extracted ladder `L(m)`. In `Corollary_t` it is written
`(m.segments.head hm).a < ((sorted (ladderRungs m)).head).a`; there the proof that the ladder
is nonempty is found from `hm`. On a concrete `m` nothing is in scope to find it from, so the
evals below spell it out (`ladderRungs_ne_nil`). -/

namespace CorollaryExamples

-- m = [(1,10), (2,3)]: both segments share depth 0, the rung is (2,10), so
-- min L(m) = 2 > 1 = min m — true.
def m_nested : Multisegment := [Segment 1 10, Segment 2 3]
#eval decide ((m_nested.segments.head (by decide)).a
  < ((sorted (ladderRungs m_nested)).head (ladderRungs_ne_nil m_nested (by decide))).a)
-- true

-- m = [(1,3)] (a single segment): L(m) = [(1,3)], so min L(m) = min m — false
-- (edge case: the condition fails on any singleton).
def m_single : Multisegment := [Segment 1 3]
#eval decide ((m_single.segments.head (by decide)).a
  < ((sorted (ladderRungs m_single)).head (ladderRungs_ne_nil m_single (by decide))).a)
-- false

-- m = [(1,3), (2,4), (3,5)] (a ladder): the single rung starts at min m — false.
def m_ladder : Multisegment := [Segment 1 3, Segment 2 4, Segment 3 5]
#eval decide ((m_ladder.segments.head (by decide)).a
  < ((sorted (ladderRungs m_ladder)).head (ladderRungs_ne_nil m_ladder (by decide))).a)
-- false

end CorollaryExamples
