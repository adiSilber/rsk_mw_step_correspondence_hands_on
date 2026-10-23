import Mathlib.Order.Interval.Basic
import Mathlib.Algebra.Order.Group.Int
import LeanProof.Fundamentals_t

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false

/-! # Segments (trusted definitions)

A segment `[a, b]` is a nonempty interval of integers. Its order, and everything built on
segments, is in `Basic_t`; what `auto_prop` needs to know about segments first is in `Segment_u`. -/

def Segment := NonemptyInterval ℤ

namespace Segment

def a (s : Segment) : ℤ := s.fst
def b (s : Segment) : ℤ := s.snd

end Segment

/-- `Segment a b` is the segment `[a, b]`; the proof of `a ≤ b` is found automatically. -/
macro_rules | `(Segment $a:term $b:term) => `(id (α := Segment) ⟨⟨$a, $b⟩, by auto_prop⟩)
