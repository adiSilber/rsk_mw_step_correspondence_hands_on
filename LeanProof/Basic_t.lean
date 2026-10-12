import Mathlib.Order.Interval.Lex
import Mathlib.Data.List.Sublists
import Mathlib.Data.Set.Lattice
import Mathlib.Data.List.Pairwise
import Mathlib.Logic.Relation
import Mathlib.Order.Interval.Basic
import Mathlib.Algebra.Order.Group.Int
import LeanProof.Fundamentals_t

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false

open scoped List

def Segment := NonemptyInterval ℤ

namespace Segment

def a (s : Segment) : ℤ := s.fst
def b (s : Segment) : ℤ := s.snd

end Segment

/-- `Segment a b` is the segment `[a, b]`; the proof of `a ≤ b` is found automatically. -/
macro_rules | `(Segment $a:term $b:term) => `((⟨⟨$a, $b⟩, by auto_prop⟩ : Segment))

/-- Segments are compared lexicographically: `s ≤ t` iff `a(s) < a(t)`, or `a(s) = a(t)` and
`b(s) ≤ b(t)`. (That this is a linear order is proved in `Basic_u`.) -/
instance : LE Segment := ⟨fun s t => s.a < t.a ∨ (s.a = t.a ∧ s.b ≤ t.b)⟩

/-- Strict precedence: Δ₁ ≪ Δ₂ iff a₁ < a₂ and b₁ < b₂. -/
def ll (s1 s2 : Segment) := s1.a < s2.a ∧ s1.b < s2.b
infix:90 " ≪ " => ll

def subsegment (s₁ s₂ : Segment) :=
  s₁.a ≥ s₂.a ∧ s₁.b ≤ s₂.b
infix:90 " ⊆ " => subsegment

/-- A list of segments that is guaranteed to be sorted lexicographically. -/
structure Multisegment where
  segments : List Segment
  is_sorted : segments.Pairwise (· ≤ ·)

def subms (ms₀ ms₁ : Multisegment) := ms₀.segments <+ ms₁.segments
infix:90 " ⊆ " => subms

/-- `n` distinct indices into `m`. -/
def Indices (n : ℕ) (m : Multisegment) : Set (List ℕ) :=
  { i | i.length = n ∧ i.Nodup ∧ ∀ k ∈ i, k < m.segments.length }
