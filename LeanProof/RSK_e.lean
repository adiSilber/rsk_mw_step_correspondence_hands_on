import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.Ladder_t
import LeanProof.Ladder_u
import LeanProof.RSK_t
import LeanProof.RSK_u

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.hashCommand false

namespace RSK

-- Interwoven example: two nested chains, depths 0 and 1. Reused by the evals below.
-- On a number line (left end = a, right end = b; ~1 char per 10 units):
--
--   1---------100           ┐
--    2------------------200 │  depth 0 bucket = {(2,200) ⊇ (4,190) ⊇ (6,180)}
--     3------90             │  depth 1 bucket = {(1,100) ⊇ (3,90)  ⊇ (5,80) }
--      4---------------190  │
--       5---80              │  rung per bucket = (max a, max b):
--        6------------180   ┘    depth 0 → (6,200),  depth 1 → (5,100)

def m_complex : Multisegment :=
  ⟨[⟨⟨1, 100⟩, by omega⟩, ⟨⟨2, 200⟩, by omega⟩, ⟨⟨3, 90⟩, by omega⟩,
    ⟨⟨4, 190⟩, by omega⟩, ⟨⟨5, 80⟩, by omega⟩, ⟨⟨6, 180⟩, by omega⟩], by decide⟩

-- Repeated segment example: the two copies of `(1,3)` lie in the same depth bucket.
-- This exposes that value-based helpers such as `bucketSucc` cannot distinguish
-- occurrences of equal segments.
def m_repeated : Multisegment :=
  ⟨[⟨⟨1, 3⟩, by omega⟩, ⟨⟨1, 3⟩, by omega⟩, ⟨⟨2, 4⟩, by omega⟩], by decide⟩

#eval bucketRung m_complex 0  -- some (6, 200)
#eval bucketRung m_complex 1  -- some (5, 100)
#eval bucketRung m_complex 2  -- none (no segment at depth 2)
#eval bucketRung m_repeated 0  -- some (2, 4)
#eval bucketRung m_repeated 1  -- some (1, 3)
#eval bucketRung m_repeated 2  -- none

#eval maxDepth m_complex  -- 1 (deepest segments sit at depth 1)
#eval maxDepth m_repeated -- 1 (the repeated `(1,3)` segments can both precede `(2,4)`)

#eval ladderRungs m_complex  -- [(5, 100), (6, 200)]
#eval ladderRungs m_repeated -- [(1, 3), (2, 4)]


#eval (residual m_complex).segments  -- [(1, 90), (2, 190), (3, 80), (4, 180)]
#eval (residual m_repeated).segments -- [(1, 3)]



end RSK
