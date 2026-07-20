
import LeanProof.Basic_t
import LeanProof.Basic_u
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Sort
-- import Mathlib.Data.Set.Finite


set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.hashCommand false

def isLadder (segments : List Segment) : Bool :=
  segments.Pairwise (· ≪ ·)


/- Computes the maximum ladder length by manually checking both conditions
    independently, requiring zero external theorems or helpers. -/
def depth_of_segment (m : Multisegment) (s : Segment) (s_in_m : s ∈ m.segments) : ℕ :=
  -- 1. Generate all computable sublists of the multisegment
  let all_sublists := m.segments.sublists
  -- 2. Filter and manually construct the Ladder structures
  let valid_ladders := all_sublists.filter (fun l => isLadder l ∧ s ∈ l.head?)
  -- 3. Extract lengths and find the maximum
  let lengths := valid_ladders.map (·.length)
  lengths.max (by
    have s_in_ladders : [s] ∈ valid_ladders := by
      simp [valid_ladders, all_sublists, s_in_m, isLadder]
    aesop) - 1


/-- Segments of `ms` at depth `d`, packaged with their `∈ ms.segments` proofs
(needed by `depth_of_segment`), sorted outermost-first by the true nesting order —
`x` comes before `y` iff `y ⊆ x`. The sort is meaningful because a bucket is a nested
family (any two of its segments are `⊆`-comparable): see `bucket_sink` and
`bucket_pairwise` in `Ladder_u`. Use `.map (·.val)` for plain segments. -/
def bucket (ms : Multisegment) (d : ℕ) : List {s : Segment // s ∈ ms.segments} :=
  (ms.segments.attach.filter fun ⟨s, hs⟩ => depth_of_segment ms s hs = d).insertionSort
    (fun x y => y.val ⊆ x.val)

/-- A multisegment whose segments form a ladder (pairwise `≪`). -/
def Ladder := {ms : Multisegment // isLadder ms.segments}
