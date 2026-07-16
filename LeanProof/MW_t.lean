import LeanProof.Basic_t
import LeanProof.Basic_u
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Chain

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.style.show false
set_option linter.hashCommand false

open scoped List

/-!
# Mœglin–Waldspurger Algorithm — trusted definitions

The MW algorithm (mirror-image / min-based version from §3.1):
1. The leading chain starts at the minimum segment (= `m.head` of the sorted list).
2. Each extension picks the first segment in the sorted tail with `a = cur_a + 1`
   and `b > cur_b` — sortedness guarantees this is the one with minimum `b`.
3. `Δ◦(m) = [a_min, a_min + k − 1]`  (k = chain length).
4. `m†`: remove chain segments; add back `[a+1, b]` for non-singletons; re-sort.
5. `m# = Δ◦(m) + (m†)#`  recursively, with `∅# = ∅`.

The greedy scan `extendChain.go` is the computational core; its proof-carrying
packagings (`extendChain`, `leadingChain`, `mwStep`) live in `MW_u`.
-/

namespace MW

/-- A "chain link" between two segments: a strict precedence `≪` with the
extra constraint that the `a`'s are consecutive. -/
def chainLink (s₁ s₂ : Segment) : Prop := s₁ ≪ s₂ ∧ s₂.a = s₁.a + 1

instance : ∀ s₁ s₂, Decidable (chainLink s₁ s₂) := by
  intro s₁ s₂; unfold chainLink; infer_instance

/-- A list of segments is a chain if each consecutive pair is a `chainLink`. -/
def isChain (segments : List Segment) : Prop := segments.IsChain chainLink

/-- The internal recursion of `extendChain`: scans `m`, appends `s` to the chain
    whenever it forms a `chainLink` with the current last. -/
def extendChain.go (m : List Segment) (chain : List Segment) (hne : chain ≠ []) : List Segment :=
  match m with
  | []      => chain
  | s :: rest =>
    if h : chainLink (chain.getLast hne) s then
      extendChain.go rest (chain ++ [s]) (by simp)
    else
      extendChain.go rest chain hne

/-- Residual of a chain segment: `[a, b] → [a+1, b]`; singletons are discarded. -/
def segmentResidual (s : Segment) : Option Segment :=
  if h : s.a < s.b then some ⟨⟨s.a + 1, s.b⟩, by omega⟩ else none

/-- Remove chain segments from `m`, add back their residuals, then re-sort. -/
def makeResidual (m : Multisegment) (chain : List Segment) : Multisegment :=
  let m_without := chain.foldl List.erase m.segments
  let residuals := chain.filterMap segmentResidual
  ⟨(m_without ++ residuals).insertionSort (· ≤ ·), List.pairwise_insertionSort _ _⟩


def mw_step (m : Multisegment) (h : m.segments ≠ []) : Segment × Multisegment :=
  let s_min := m.segments.head h
  let chain := extendChain.go m.segments [s_min] (by simp)
  let k := chain.length
  let delta_circ := ⟨⟨s_min.a, s_min.a + ↑(k - 1)⟩, by omega⟩
  let residual := makeResidual m chain
  (delta_circ, residual)

end MW
