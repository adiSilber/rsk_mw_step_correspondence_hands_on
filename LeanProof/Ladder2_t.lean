import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.Ladder1_t
import LeanProof.Ladder1_u
import Mathlib.Data.Finset.Max

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false

/-- d(Δ) = max `depthSet m s` (finite by `Ladder1_u`, nonempty since `0` is in it). -/
def depth_of_segment (m : Multisegment) (s : Segment) (hs : s ∈ m.segments) : ℕ :=
  maximum (depthSet m s)

def isLadder (segments : List Segment) : Bool :=
  segments.Pairwise (· ≪ ·)

/-- `𝔡⁻¹(d)`: the segments of `ms` at depth `d`, in the order of `ms`, each with its proof of
`∈ ms.segments`. (Their nested order comes from an admissible enumeration, see `RSK1_t`.) -/
def bucket (ms : Multisegment) (d : ℕ) : List {s : Segment // s ∈ ms.segments} :=
  [s ∈ ms.segments | depth_of_segment ms s = d]

/-- A multisegment whose segments form a ladder (pairwise `≪`). -/
def Ladder := {ms : Multisegment // isLadder ms.segments}

/-- Paper, §2: "choose an admissible enumeration `{i₁, …, i_l}` of `𝔡⁻¹(k)`, namely such
that `Δ_{i₁} ⊃ … ⊃ Δ_{i_l}`". This is the set of all such enumerations (here numbered
`i₀, …, i_l`). -/
def admissibleEnumerations (m : Multisegment) (k : ℕ) : Set (List ℕ) :=
  { i |
    -- i = i₀, …, i_l, distinct indices into m
    ∃ l : {l : ℕ // (i ∈ Indices l m)},
    -- {i₀, …, i_l} = 𝔡⁻¹(k)
    (∀ n : Fin m.segments.length, (↑n ∈ i ↔ depth_of_segment m m.segments[n] = k)) ∧
    -- Δ_{i₀} ⊃ … ⊃ Δ_{i_l}
    (∀ r : ℕ, r < l → m.segments[i[r + 1]] ⊆ m.segments[i[r]]) }
