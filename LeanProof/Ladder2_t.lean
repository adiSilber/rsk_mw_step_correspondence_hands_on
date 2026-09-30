import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.Ladder1_t
import LeanProof.Ladder1_u
import Mathlib.Data.Finset.Max

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false

/-- d(Δ) = max `depthSet m s` (finite by `Ladder1_u`, nonempty since `0` is in it). -/
def depth_of_segment (m : Multisegment) (s : Segment) (hs : ⟮s ∈ m.segments⟯) : ℕ :=
  maximum (depthSet m s)

def isLadder (segments : List Segment) : Bool :=
  segments.Pairwise (· ≪ ·)

/-- Segments of `ms` at depth `d`, packaged with their `∈ ms.segments` proofs
(needed by `depth_of_segment`), sorted outermost-first by the true nesting order —
`x` comes before `y` iff `y ⊆ x`. The sort is meaningful because a bucket is a nested
family (any two of its segments are `⊆`-comparable). Use `.map (·.val)` for plain
segments. -/
def bucket (ms : Multisegment) (d : ℕ) : List {s : Segment // s ∈ ms.segments} :=
  [s ∈ ms.segments | depth_of_segment ms s = d].insertionSort (fun x y => y.val ⊆ x.val)

/-- A multisegment whose segments form a ladder (pairwise `≪`). -/
def Ladder := {ms : Multisegment // isLadder ms.segments}
