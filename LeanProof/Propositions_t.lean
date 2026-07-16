import LeanProof.RSK_t
import LeanProof.RSK_u
import LeanProof.MW_t

def min_m_lt_min_lm (m : Multisegment) (h : m.segments ≠ []) : Prop :=
  (m.segments.head h).a < ((RSK.ladderRungs m).head (RSK.ladderRungs_ne_nil m h)).a
