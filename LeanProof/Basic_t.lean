import Mathlib.Order.Interval.Lex
import Mathlib.Data.List.Sublists
import Mathlib.Data.Set.Lattice
import Mathlib.Data.List.Pairwise
import Mathlib.Logic.Relation
import Mathlib.Order.Interval.Basic
import Mathlib.Algebra.Order.Group.Int
import LeanProof.Fundamentals_t
import LeanProof.Segment_t
import LeanProof.Segment_u

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false

open scoped List

/-- Segments are compared lexicographically, by `a` then by `b`: `s ≤ t` iff `a(s) < a(t)`, or
`a(s) = a(t)` and `b(s) ≤ b(t)`. (The order of `ℤ ×ₗ ℤ`, pulled back.) -/
instance : LinearOrder Segment := LinearOrder.lift' (fun s => toLex (s.a, s.b))

/-- Strict precedence: Δ₁ ≪ Δ₂ iff a₁ < a₂ and b₁ < b₂. -/
abbrev ll (s1 s2 : Segment) : Prop := s1.a < s2.a ∧ s1.b < s2.b
infix:90 " ≪ " => ll

abbrev subsegment (s₁ s₂ : Segment) : Prop :=
  s₁.a ≥ s₂.a ∧ s₁.b ≤ s₂.b
infix:90 " ⊆ " => subsegment

/-- A list of segments that is guaranteed to be sorted lexicographically. -/
structure Multisegment where
  segments : List Segment
  is_sorted : segments.Pairwise (· ≤ ·)

/-- `Σ Δ`: a list of segments is read as the multisegment of its segments in increasing order
(repeats kept); used silently wherever a `Multisegment` is expected and a list is given. -/
instance : Coe (List Segment) Multisegment := ⟨fun l => Multisegment.mk l.increasing⟩

abbrev subms (ms₀ ms₁ : Multisegment) : Prop := ms₀.segments <+ ms₁.segments
infix:90 " ⊆ " => subms

/-- `n` distinct indices into `m`. -/
def Indices (n : ℕ) (m : Multisegment) : Set (List ℕ) :=
  { i | i.length = n ∧ i.Nodup ∧ ∀ k ∈ i, k < m.segments.length }
