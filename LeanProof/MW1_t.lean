import LeanProof.Basic_t
import LeanProof.Basic_u
import Mathlib.Data.List.Chain

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false

/-!
# Mœglin–Waldspurger, part 1: leading indices (trusted definitions)

Paper §MW: the leading indices `i₁, …, i_k` of a multisegment `m`.
-/

namespace MW

abbrev chainLink (s₁ s₂ : Segment) : Prop := s₁ ≪ s₂ ∧ s₂.a = s₁.a + 1

abbrev isChain (segments : List Segment) : Prop := segments.IsChain chainLink

def Chain := {ms : Multisegment // isChain ms.segments}

def segmentResidual (s : Segment) (h : s.a < s.b) : Segment :=
  Segment (s.a + 1) s.b

abbrev isFirst (m : Multisegment) (s : Segment) : Prop :=
  s ∈ m.segments ∧ ∀ t ∈ m.segments, s ≤ t

abbrev isNext (m : Multisegment) (s t : Segment) : Prop :=
  t ∈ m.segments ∧ chainLink s t ∧ ∀ u ∈ m.segments, chainLink s u → t ≤ u

abbrev isLast (m : Multisegment) (s : Segment) : Prop :=
  ∀ t ∈ m.segments, ¬ chainLink s t

def leadingIndices (m : Multisegment) : Set (List ℕ) :=
  { i : List ℕ | ∃ k : {k : ℕ // i ∈ Indices k m ∧ 0 < k},
        isFirst m m.segments[i[0]] ∧
        (∀ j : ℕ, j + 1 < k → isNext m m.segments[i[j]] m.segments[i[j + 1]]) ∧
        (∀ j : ℕ, j + 1 = k → isLast m m.segments[i[j]]) }

end MW
