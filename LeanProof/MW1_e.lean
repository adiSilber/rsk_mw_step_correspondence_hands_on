import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.MW1_t
import LeanProof.MW1_u

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.hashCommand false

namespace MW1Examples
open MW

-- (1,3) → (2,4): 2 = 1+1 and 3 < 4 — chain link.
#eval decide (chainLink (Segment 1 3) (Segment 2 4))   -- true
-- (1,3) → (3,5): a's jump from 1 to 3 (must be consecutive) — not a chain link.
#eval decide (chainLink (Segment 1 3) (Segment 3 5))   -- false
-- (1,5) → (2,4): a's ok, but b doesn't strictly increase (5 → 4) — not a chain link.
#eval decide (chainLink (Segment 1 5) (Segment 2 4))   -- false
-- (1,3) → (2,3): a's ok, but b ties (3 → 3, must be strict) — not a chain link.
#eval decide (chainLink (Segment 1 3) (Segment 2 3))   -- false

-- A chain: a's go 1,2,3 and b's are strictly increasing.
#eval decide (isChain [Segment 1 3, Segment 2 4, Segment 3 5])   -- true
-- Not a chain: a's jump from 1 to 5 (must be consecutive).
#eval decide (isChain [Segment 1 3, Segment 5 7])   -- false
-- Not a chain: b doesn't strictly increase.
#eval decide (isChain [Segment 1 5, Segment 2 4])   -- false

/-! ### `segmentResidual`: ⁻Δ = [a+1, b], for a segment that is not a single point -/
#eval segmentResidual (Segment 1 3)   -- (2, 3)
#eval segmentResidual (Segment 1 2)   -- (2, 2)
-- (`segmentResidual (Segment 1 1)` does not type-check: ⁻[1,1] is empty.)

-- m = [(1,2), (1,4), (2,3), (2,5), (5,7)]: sorted; (1,2) is least; after (1,2) both (2,3)
-- and (2,5) are chain-linked, the least being (2,3); nothing is linked to (2,3) or (5,7).
def m_fork : Multisegment := [Segment 1 2, Segment 1 4, Segment 2 3, Segment 2 5, Segment 5 7]

#eval decide (isNext m_fork (Segment 1 2) (Segment 2 3))   -- true  (least link after (1,2))
#eval decide (isNext m_fork (Segment 1 2) (Segment 2 5))   -- false (linked, but not least)
#eval decide (isNext m_fork (Segment 1 4) (Segment 2 5))   -- true  ((2,3) is not linked to (1,4))
#eval decide (isLast m_fork (Segment 2 3))   -- true  (no segment begins at 3)
#eval decide (isLast m_fork (Segment 1 2))   -- false

/-! ### `leadingIndices`: the sequences i₁, …, i_k of positions in `m` (paper (a)–(c)) -/
#eval decide ([0, 2] ∈ leadingIndices m_fork)   -- true:  (1,2), (2,3)
#eval decide ([0, 3] ∈ leadingIndices m_fork)   -- false: (2,5) is not the least link
#eval decide ([0] ∈ leadingIndices m_fork)      -- false: (1,2) is not last
#eval decide ([1, 3] ∈ leadingIndices m_fork)   -- false: (1,4) is not the least segment
#eval (leadingIndices m_fork).toFinset          -- {[0, 2]}

-- Repeated segments: m = [(1,1), (1,1), (2,2)] — two sequences of leading indices.
def m_twice : Multisegment := [Segment 1 1, Segment 1 1, Segment 2 2]
#eval (leadingIndices m_twice).toFinset         -- {[0, 2], [1, 2]}
#eval first (leadingIndices m_twice)            -- [0, 2]

/-! ### The greedy scan (`MW1_u`): how a sequence of leading indices is found -/
-- Scanning [(2,4),(3,5)] from the chain [(1,3)]: both link.
#eval extendChain.go [Segment 2 4, Segment 3 5] [Segment 1 3] (by simp)   -- [(1,3),(2,4),(3,5)]
-- Scanning [(2,4),(5,7)]: (2,4) links, (5,7) does not (a jumps 2 → 5).
#eval extendChain.go [Segment 2 4, Segment 5 7] [Segment 1 3] (by simp)   -- [(1,3),(2,4)]
#eval (greedyChain m_fork).val.segments    -- [(1, 2), (2, 3)]
#eval (greedyChain m_twice).val.segments   -- [(1, 1), (2, 2)]

end MW1Examples
