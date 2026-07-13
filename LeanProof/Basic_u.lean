import Mathlib.Order.Interval.Lex
import Mathlib.Data.List.Sublists
import Mathlib.Data.Set.Lattice
import Mathlib.Data.List.Pairwise
import Mathlib.Logic.Relation
import Mathlib.Order.Interval.Basic
import Mathlib.Algebra.Order.Group.Int
import LeanProof.Basic_t
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false

open scoped List

/-! # Shared basic definitions for the RSK / Mœglin–Waldspurger development.

The `Segment` type, its accessors, and the `Multisegment` (a sorted list of
segments) are used by both `LeanProof.LadderMinimal` and
`LeanProof.MultiSegments`.
-/


-- /-- Left shift of a segment: `[a,b] ↦ [a-1,b-1]`, written as `\lshft Δ` in the paper. -/
-- def leftShift (s : Segment) : Segment :=
--   ⟨⟨s.a - 1, s.b - 1⟩, by
--     simpa [a, b, sub_eq_add_neg] using Int.add_le_add_right s.fst_le_snd (-1)⟩


instance : DecidableEq Segment := inferInstanceAs (DecidableEq (NonemptyInterval ℤ))

instance : Repr Segment where
  reprPrec s _ := reprPrec (s.a, s.b) 0

/-- The explicit description of the lexicographic order on segments. -/
lemma Segment.le_def (s₁ s₂ : Segment) :
    s₁ ≤ s₂ ↔ s₁.a < s₂.a ∨ (s₁.a = s₂.a ∧ s₁.b ≤ s₂.b) :=
  Prod.Lex.le_iff

instance : ∀ x y, Decidable (x ≪ y) := by
  intro x y; simp [(· ≪ ·)]; infer_instance

@[trans]
lemma ll_trans x y z : x ≪ y → y ≪ z → x ≪ z := by
  simp [(· ≪ ·)]; omega

instance : Transitive (· ≪ ·) := ll_trans


instance : ∀(s₁ s₂ : Segment), Decidable (s₁ ⊆ s₂) := by
  unfold subsegment; infer_instance
