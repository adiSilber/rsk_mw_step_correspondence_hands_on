import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.MW1_t
import LeanProof.MW1_u

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false

/-!
# Mœglin–Waldspurger, part 2: one step `MW(m) = (Δ^MW(m), m^MW)` (trusted definitions)

Paper §MW: for a nonzero multisegment `m`, with `i₁, …, i_k` a sequence of leading indices
(any one), the leading chain `Δ_{i₁}, …, Δ_{i_k}`, the multisegment `m^MW = Σ Δ_j^*` and the
segment `Δ^MW(m) = [b(Δ_{i₁}), b(Δ_{i₁}) + k − 1]`.
-/

def leadingChain (m : Multisegment) (h : m.segments ≠ []) : List Segment :=
  let i ∈ leadingIndices m; [m.segments[j] | j ∈ i]

def makeResidual (m : Multisegment) (h : m.segments ≠ []) : Multisegment :=
  let i ∈ leadingIndices m;
  [m.segments[j] | j < m.segments.length, j ∉ i]
    ++ [segmentResidual m.segments[j] | j ∈ i, m.segments[j].a < m.segments[j].b]

def deltaCirc (m : Multisegment) (h : m.segments ≠ []) : Segment :=
  let i ∈ leadingIndices m; Segment m.segments[i[0]].a m.segments[i[i.length - 1]].a

def mw_step (m : Multisegment) (h : m.segments ≠ []) : Segment × Multisegment :=
  (deltaCirc m, makeResidual m)
