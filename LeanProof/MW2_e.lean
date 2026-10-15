import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.MW1_t
import LeanProof.MW1_u
import LeanProof.MW2_t
import LeanProof.MW2_u

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.hashCommand false

namespace MW2Examples
open MW

def m_full : Multisegment := [Segment 1 3, Segment 2 4, Segment 3 5, Segment 4 6]
def m_break : Multisegment := [Segment 1 3, Segment 2 4, Segment 5 7]
def m_fork : Multisegment := [Segment 1 2, Segment 1 4, Segment 2 5]
def m_points : Multisegment := [Segment 1 1, Segment 2 2, Segment 3 3]
def m_single : Multisegment := [Segment 7 7]
def m_twice : Multisegment := [Segment 1 1, Segment 1 1, Segment 2 3, Segment 4 6]

/-! ### `leadingChain`: Δ_{i₁}, …, Δ_{i_k} -/
#eval leadingChain m_full     -- [(1, 3), (2, 4), (3, 5), (4, 6)]: every segment links up
#eval leadingChain m_break    -- [(1, 3), (2, 4)]: no segment begins at 3
#eval leadingChain m_fork     -- [(1, 2), (2, 5)]: (1,2) is least, then (2,5) (5 > 2)
#eval leadingChain m_points   -- [(1, 1), (2, 2), (3, 3)]: singletons link up
#eval leadingChain m_single   -- [(7, 7)]

/-! ### `makeResidual`, `deltaCirc`: m^MW and Δ^MW(m) -/
#eval (makeResidual m_break).segments   -- [(2, 3), (3, 4), (5, 7)]
#eval deltaCirc m_break                 -- (1, 2)
-- (1,1) twice: one copy is leading and loses its only point, the other stays
#eval (makeResidual m_twice).segments   -- [(1, 1), (3, 3), (4, 6)]
#eval (makeResidual m_points).segments  -- []: three singletons, all leading, nothing is left
#eval deltaCirc m_points                -- (1, 3)

/-! ### `mw_step`: (Δ^MW(m), m^MW) -/
#eval ((mw_step m_full).1, (mw_step m_full).2.segments)
  -- ((1, 4), [(2, 3), (3, 4), (4, 5), (5, 6)]): all leading, each loses its first point
#eval ((mw_step m_single).1, (mw_step m_single).2.segments)   -- ((7, 7), [])
#eval ((mw_step m_twice).1, (mw_step m_twice).2.segments)   -- ((1, 2), [(1, 1), (3, 3), (4, 6)])
-- (The empty multisegment is not an input: `mw_step` needs `m.segments ≠ []`, as in the paper.)

end MW2Examples
