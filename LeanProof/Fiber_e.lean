import LeanProof.Fiber_t
import LeanProof.Fiber_u
import LeanProof.RSK_e

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.hashCommand false

-- fiber m_ladder d (depths are 2, 1, 0 for (1,3), (2,4), (3,5)) — singletons, same as bucket:
-- fiber 0 = [(3,5)], fiber 1 = [(2,4)], fiber 2 = [(1,3)]
#eval (fiber m_ladder 0).map (·.val)
#eval (fiber m_ladder 1).map (·.val)
#eval (fiber m_ladder 2).map (·.val)

-- fiber m_mixed d (depths are 1, 1, 0 for (1,3), (1,4), (2,5)):
-- unlike the bucket (in `ms` order), the fiber is sorted outermost-first:
-- (1,3) ⊆ (1,4), so fiber 1 = [(1,4), (1,3)]; fiber 0 = [(2,5)], fiber 2 = []
#eval (fiber m_mixed 0).map (·.val)
#eval (fiber m_mixed 1).map (·.val)
#eval (fiber m_mixed 2).map (·.val)
