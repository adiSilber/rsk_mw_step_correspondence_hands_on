import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.MW_t
import LeanProof.MW_u

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.hashCommand false

namespace MoeglinWaldspurger

/-- Example-file convenience: sort a list of segments into a `Multisegment`. -/
def msOf (l : List Segment) : Multisegment :=
  ⟨l.insertionSort (· ≤ ·), List.pairwise_insertionSort _ _⟩

-- (1,3) → some (2,3)
#eval segmentResidual ⟨⟨1, 3⟩, by omega⟩
-- (1,1) singleton → none
#eval segmentResidual ⟨⟨1, 1⟩, by omega⟩

-- Example 1: m = [(1,3),(2,4),(5,7)], chain = [(1,3),(2,4)].
-- Chain removed; residuals (1,3)→(2,3), (2,4)→(3,4). Expected: [(2,3),(3,4),(5,7)].
def m₁ : Multisegment := msOf
  [⟨⟨1, 3⟩, by omega⟩, ⟨⟨2, 4⟩, by omega⟩, ⟨⟨5, 7⟩, by omega⟩]
def chain₁ : List Segment :=
  [⟨⟨1, 3⟩, by omega⟩, ⟨⟨2, 4⟩, by omega⟩]
#eval (makeResidual m₁ chain₁).segments

-- Example 2: m has (1,1) twice, chain has it once.
-- (1,1) singleton → no residual; (2,3) → (3,3). Expected: [(1,1),(3,3),(4,6)].
def m₂ : Multisegment := msOf
  [⟨⟨1, 1⟩, by omega⟩, ⟨⟨1, 1⟩, by omega⟩, ⟨⟨2, 3⟩, by omega⟩, ⟨⟨4, 6⟩, by omega⟩]
def chain₂ : List Segment :=
  [⟨⟨1, 1⟩, by omega⟩, ⟨⟨2, 3⟩, by omega⟩]
#eval (makeResidual m₂ chain₂).segments

-- Example 3: every chain segment is a singleton → all residuals discarded. Expected: [].
def m₃ : Multisegment := msOf
  [⟨⟨1, 1⟩, by omega⟩, ⟨⟨2, 2⟩, by omega⟩]
def chain₃ : List Segment :=
  [⟨⟨1, 1⟩, by omega⟩, ⟨⟨2, 2⟩, by omega⟩]
#eval (makeResidual m₃ chain₃).segments

-- (1,3) → (2,4): 2 = 1+1 and 3 < 4 — chain link.
#eval decide (chainLink (⟨⟨1, 3⟩, by omega⟩ : Segment) ⟨⟨2, 4⟩, by omega⟩)
-- (1,3) → (3,5): a's jump from 1 to 3 (must be consecutive) — not a chain link.
#eval decide (chainLink (⟨⟨1, 3⟩, by omega⟩ : Segment) ⟨⟨3, 5⟩, by omega⟩)
-- (1,5) → (2,4): a's ok, but b doesn't strictly increase (5 → 4) — not a chain link.
#eval decide (chainLink (⟨⟨1, 5⟩, by omega⟩ : Segment) ⟨⟨2, 4⟩, by omega⟩)
-- (1,3) → (2,3): a's ok, but b ties (3 → 3, must be strict) — not a chain link.
#eval decide (chainLink (⟨⟨1, 3⟩, by omega⟩ : Segment) ⟨⟨2, 3⟩, by omega⟩)

-- A chain: a's go 1,2,3 and b's are strictly increasing.
#eval decide (isChain
  [(⟨⟨1, 3⟩, by omega⟩ : Segment), ⟨⟨2, 4⟩, by omega⟩, ⟨⟨3, 5⟩, by omega⟩])
-- Not a chain: a's jump from 1 to 5 (must be consecutive).
#eval decide (isChain
  [(⟨⟨1, 3⟩, by omega⟩ : Segment), ⟨⟨5, 7⟩, by omega⟩])
-- Not a chain: b doesn't strictly increase.
#eval decide (isChain
  [(⟨⟨1, 5⟩, by omega⟩ : Segment), ⟨⟨2, 4⟩, by omega⟩])

-- A singleton chain `[(1,3)]` reused as the starting chain in the cases below.
def init_chain : Chain :=
  ⟨⟨[⟨⟨1, 3⟩, by omega⟩], by decide⟩, by decide⟩

-- Case A: scanning [(2,4),(3,5)] — both link. Expected: [(1,3),(2,4),(3,5)].
#eval (extendChain
  (msOf [⟨⟨2, 4⟩, by omega⟩, ⟨⟨3, 5⟩, by omega⟩])
  init_chain (by decide)).val.segments

-- Case B: scanning [(2,4),(5,7)] — (2,4) links, (5,7) breaks (a jumps 2→5).
-- Expected: [(1,3),(2,4)].
#eval (extendChain
  (msOf [⟨⟨2, 4⟩, by omega⟩, ⟨⟨5, 7⟩, by omega⟩])
  init_chain (by decide)).val.segments

-- Case C: scanning [(5,7)] — doesn't link with (1,3). Expected: [(1,3)].
#eval (extendChain
  (msOf [⟨⟨5, 7⟩, by omega⟩])
  init_chain (by decide)).val.segments

-- m = [[1,3],[2,4],[3,5],[4,6]] → full chain: all four segments
#eval (leadingChain
  (msOf
    [⟨⟨1, 3⟩, by omega⟩, ⟨⟨2, 4⟩, by omega⟩, ⟨⟨3, 5⟩, by omega⟩, ⟨⟨4, 6⟩, by omega⟩])).val.segments

-- m = [[1,3],[2,4],[5,7]] → chain stops at [2,4] (no segment with a=3)
#eval (leadingChain
  (msOf
    [⟨⟨1, 3⟩, by omega⟩, ⟨⟨2, 4⟩, by omega⟩, ⟨⟨5, 7⟩, by omega⟩])).val.segments

-- m = [[1,2],[1,4],[2,5]] → takes [1,2] first (sorted), then [2,5] (b=5 > 2)
#eval (leadingChain
  (msOf
    [⟨⟨1, 2⟩, by omega⟩, ⟨⟨1, 4⟩, by omega⟩, ⟨⟨2, 5⟩, by omega⟩])).val.segments

-- m = [[1,1],[2,2],[3,3]] → singleton chain: all three link up
#eval (leadingChain
  (msOf
    [⟨⟨1, 1⟩, by omega⟩, ⟨⟨2, 2⟩, by omega⟩, ⟨⟨3, 3⟩, by omega⟩])).val.segments

-- m = [[1,3],[2,4],[3,5],[4,6]] → chain is all four, Δ◦ = [1,4], m† = [[2,3],[3,4],[4,5],[5,6]]
#eval (fun p : Segment × Multisegment => (p.1, p.2.segments))
  (mw_step (msOf
    [⟨⟨1, 3⟩, by omega⟩, ⟨⟨2, 4⟩, by omega⟩, ⟨⟨3, 5⟩, by omega⟩, ⟨⟨4, 6⟩, by omega⟩])
    (by decide))

-- m = [[1,1],[2,2]] → chain = [(1,1),(2,2)], Δ◦ = [1,2], m† = [] (both singletons)
#eval (fun p : Segment × Multisegment => (p.1, p.2.segments))
  (mw_step (msOf
    [⟨⟨1, 1⟩, by omega⟩, ⟨⟨2, 2⟩, by omega⟩])
    (by decide))

-- m = ∅: `mw_step` requires a nonemptiness proof, so the empty case cannot be called.

end MoeglinWaldspurger
