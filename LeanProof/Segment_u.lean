import LeanProof.Segment_t

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false

/-! # Segments: what `auto_prop` knows about them

Used by `Basic_t` (the proof omitted in the definition of the order on segments) and by
`Segment a b` everywhere. -/

-- `a` and `b` may be unfolded, and an interval is determined by its two ends: together these
-- give that `s ↦ (a s, b s)` is injective, the proof the linear order of `Basic_t` omits.
attribute [grind] Segment.a Segment.b
attribute [grind →] NonemptyInterval.ext

/-- Every segment satisfies `a ≤ b`; `grind` learns it whenever it meets `s.a` or `s.b`. -/
lemma Segment.a_le_b (s : Segment) : s.a ≤ s.b := s.fst_le_snd
grind_pattern Segment.a_le_b => s.a
grind_pattern Segment.a_le_b => s.b

/-- A segment prints as the pair of its ends (for the `_e` files). -/
instance : Repr Segment := ⟨fun s _ => repr (s.a, s.b)⟩
