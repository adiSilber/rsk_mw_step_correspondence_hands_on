import Mathlib.Order.Interval.Lex
import Mathlib.Data.List.Sublists
import Mathlib.Data.Set.Lattice
import Mathlib.Data.List.Pairwise
import Mathlib.Logic.Relation
import Mathlib.Order.Interval.Basic
import Mathlib.Algebra.Order.Group.Int

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false

open scoped List

def Segment := NonemptyInterval ℤ

namespace Segment

def a (s : Segment) : ℤ := s.fst
def b (s : Segment) : ℤ := s.snd

/-- The length of a segment as a `ℕ`. -/
def length (s : Segment) : ℕ := (s.b - s.a).toNat + 1

end Segment

def leq (s1 s2 : Segment) := s1.a < s2.a ∨ (s1.a = s2.a ∧ s1.b ≤ s2.b)
infix:90 " ≤ " => leq

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
