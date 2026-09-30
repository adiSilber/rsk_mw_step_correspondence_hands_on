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

instance : ∀ (ms₀ ms₁ : Multisegment), Decidable (ms₀ ⊆ ms₁) := by
  unfold subms; infer_instance

/-! ### `maximum` of `{f x | x ∈ l}` -/

lemma maximum_mem {α} [LinearOrder α] (S : Set α) [Fintype S] (h : S.Nonempty) :
    maximum S h ∈ S := Set.mem_toFinset.mp (Finset.max'_mem _ _)

lemma le_maximum {α} [LinearOrder α] (S : Set α) [Fintype S] (h : S.Nonempty) {x : α}
    (hx : x ∈ S) : x ≤ maximum S h := Finset.le_max' _ _ (Set.mem_toFinset.mpr hx)

/-- `{f x | x ∈ l}` is finite: it is computed by `l.map f`. -/
instance {α β} [DecidableEq β] (l : List α) (f : α → β) : Fintype {y | ∃ x ∈ l, f x = y} :=
  Fintype.ofFinset (l.map f).toFinset (by simp)

lemma nonempty_image_cons {α β} (s : α) (ss : List α) (f : α → β) :
    {y | ∃ x ∈ s :: ss, f x = y}.Nonempty := ⟨f s, s, List.mem_cons_self, rfl⟩

/-- The largest begin point of a list of segments is at most its largest end point. -/
lemma maximum_a_le_maximum_b (l : List Segment) (h₁ h₂) :
    maximum {(x.a) | x ∈ l} h₁ ≤ maximum {(x.b) | x ∈ l} h₂ := by
  obtain ⟨x, hx, hxa⟩ := maximum_mem {(x.a) | x ∈ l} h₁
  rw [← hxa]
  exact le_trans x.fst_le_snd (le_maximum _ h₂ ⟨x, hx, rfl⟩)

-- Teach `auto_prop` (the tactic behind `⟮p⟯` arguments) the two facts above.
macro_rules | `(tactic| auto_prop) => `(tactic| exact nonempty_image_cons _ _ _)
macro_rules | `(tactic| auto_prop) => `(tactic| exact maximum_a_le_maximum_b _ _ _)

-- Lets the index rule of `Fundamentals_t` unfold `Indices`.
attribute [grind =] Indices

instance (j : ℕ) (m : Multisegment) (i : List ℕ) : Decidable (i ∈ Indices j m) := by
  unfold Indices; infer_instance
