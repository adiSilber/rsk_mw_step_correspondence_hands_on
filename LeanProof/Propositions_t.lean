import LeanProof.RSK3_t
import LeanProof.RSK3_u
import LeanProof.MW1_t
import LeanProof.MW1_u
import LeanProof.MW2_t
import LeanProof.MW2_u

def min_m_lt_min_lm (m : Multisegment) (h : m.segments ≠ []) : Prop :=
  (m.segments.head h).a < ((sorted (ladderRungs m)).head).a
