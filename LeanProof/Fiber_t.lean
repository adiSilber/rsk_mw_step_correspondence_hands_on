import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.RSK_t

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false

/-- The fiber of the depth function over `d`: the segments of `ms` at depth `d`
(`bucket ms d`), sorted outermost-first by the true nesting order — `x` comes before `y`
iff `y ⊆ x`. Sorting by `⊆` produces a genuinely nested chain because a bucket is a
nested family (any two of its segments are `⊆`-comparable; see `bucket_sink` and
`fiber_nested` in the untrusted files). -/
def fiber (ms : Multisegment) (d : ℕ) : List {s : Segment // s ∈ ms.segments} :=
  (bucket ms d).insertionSort (fun x y => y.val ⊆ x.val)
