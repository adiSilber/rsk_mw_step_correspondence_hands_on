# RSK / MW step correspondence, by trust level

A restructured take on the single RSK/MW step from Gurevich–Lapid, *RSK for
multisegments* (`RSK040521.tex` in this repo), formalized in Lean 4 + Mathlib.
The development is organized by **trust level**: for each part of the proof,

- `*_t` files hold the **trusted definitions** (segments, ladders, the RSK step,
  the MW algorithm) — the short files a human must check against the paper;
- `*_u` files **prove them correct** (e.g. Lemma 2.2 / Corollary 2.3, the
  greedy-chain analysis, and ultimately Corollary 3.4) — nothing here needs to
  be read to trust the statements;
- `*_e` files hold **executable examples** (`#eval`s) exercising the trusted
  definitions on small inputs.

Two conventions keep the trusted surface honest:

- **Every `_t` definition has evals.** Each definition in a `_t` file is
  exercised by `#eval`s in its part's `_e` file, including edge cases (empty
  multisegments, singleton segments/buckets, repeated segments, failing side
  conditions), with the expected output recorded in a comment.
- **The trusted surface is minimal.** A definition earns a place in a `_t` file
  only if trusted statements or later parts genuinely need it; anything that
  can instead be a `private` def inside a `_u` file is made private there
  (e.g. `depthFinset`, the algorithm computing `depthSet`, is private in
  `Ladder1_u`, not a trusted def).

The final result is `corollary_3_4` in `LeanProof/Corollary_t.lean`:
`(K × Id)(MW(m)) = (Id × MW)(K(m))` for `min m < min L(m)` — the RSK step and
the MW step commute (ladders agree, MW segments agree, remainders agree).
`#print axioms corollary_3_4` reports only `propext, Classical.choice,
Quot.sound`: no `sorry`, no extra axioms.

## Import discipline

The parts are layered with a strict import discipline:

- a part's `_t` file imports the `_t` and `_u` files of the part just **below** it
  (`Segment_t` imports `Fundamentals_t`);
- a part's `_u` file imports the `_u` file of the part just below it and its **own** `_t`;
- Lean imports are transitive, so each file sees everything below it; the import
  block names only the step;
- a part's `_e` file may depend on the `_t` and `_u` files of its **own** part
  and of earlier ones (e.g. `Basic_e` uses `Basic_u`'s decidability
  instances, and `MW1_e` uses `MW1_u` to demonstrate the greedy scan). Nothing
  imports an `_e` file, so this adds nothing to the trusted surface.

Definitions and lemmas in a `_u` file are `private`, unless a later file needs them (`tools/Unused.lean`
lists the public ones used only in their own file). Such a
public proof-side definition lives in the namespace `Proof`, which is **never opened**, so it
can only be meant by its full name — e.g. `Proof.sortedBucket` (in `Ladder2_u`: the bucket
sorted by nesting; `RSK1_u` proves `fiber m k` equals it). No `_t` or `_e` file names a
`Proof.*` definition, so none appears in a trusted statement, and a `_u` file can never change
what a `_t` statement means by adding one. (The full name is the protection, not the file:
Lean imports are transitive, so a `_t` file sees every definition of the `_u` files below it.)
Two greps check the rule; both must print nothing:

```sh
grep -rnE '^\s*open\b.*\bProof\b' LeanProof/                                # nothing opens Proof
grep -nE '(^|[^A-Za-z0-9_.])Proof\.' LeanProof/*_t.lean LeanProof/*_e.lean  # no _t/_e names Proof.*
```

"Earlier" refers not to a single linear chain but to the dependency **tree**
below.

## Dependency tree

```
Fundamentals   project-wide rules and notation: omitted proof arguments and `l[i]`
               bounds are found by `auto_prop` (= `grind`, taught facts in `_u` files),
               `maximum` and `sorted` of a finite set, `let x ∈ S; e` (an arbitrary
               element, when `e` does not depend on it), the set comprehension `{f | x ∈ l}`
               and list comprehensions `[x ∈ l | p]`
               and `[f | x ∈ l, (y, z) ∈ l', k ≤ n, p, …]` (a bare `p` keeps the choices
               satisfying it; a fact `f` needs and the binders do not give becomes a
               condition too),
               `p → q` keeps `p` in scope for `q`,
               `x ∈ s` converts `x` to the element type of `s`, by an injective
               conversion only (`Fin → ℕ`, subtype → base, `ℕ`/`ℤ` into a `CharZero`
               type), any other is refused; below everything
Segment        segments (= NonemptyInterval ℤ), `Segment a b`; Segment_u: what auto_prop
               knows about them (a, b unfold; an interval is determined by its ends; a ≤ b)
Basic          lex order on segments, lists of segments read as multisegments (coercion),
               multisegments, ≪, ⊆, Indices (index lists into a multisegment)
├── Ladder1    depthSet (the paper's depth set, by set comprehension);
│   │          Ladder1_u proves it finite by computing it (depthFinset)
│   └── Ladder2   depth_of_segment (= max of depthSet), isLadder, bucket, Ladder,
│       │         admissibleEnumerations (Ladder2_u: finite, nonempty for nonempty fibers)
│       └── RSK1  fiber (the segments of 𝔡⁻¹(k) in the order of an admissible
│           │     enumeration — any one; Ladder2_u proves they all agree)
│           └── RSK2  bucketRung
│               └── RSK3  maxDepth, ladderRungs, bucketResidual, residual, rsk_step
│                         (maxDepth, residual and rsk_step take `m ≠ 0`, as in the paper)
└── MW1        chainLink, isChain, Chain, segmentResidual (⁻Δ), isFirst, isNext, isLast,
    │          leadingIndices (the paper's (a)–(c)); MW1_u: the greedy scan finds one, and
    │          all give the same segments
    └── MW2    makeResidual (m^MW), deltaCirc (Δ^MW), mw_step, by the paper's
               formulas over a sequence of leading indices (any one — MW1_u proves the
               result does not depend on it)
               (MW depends on Basic only — RSK and MW are independent)

RSK + MW ──► Lemmas_u   proofs only — everything `corollary_3_4` needs beyond the trusted
                        definitions (Lemma 2.1/2.2 API, Δ°-preservation, ladder preservation,
                        the derived-pair counting calculus and telescoping), ending with
                        deltaCirc_eq_of_residual, mw_preserves_ladder, mw_residual_commute
             └── Corollary  corollary_3_4, with its side condition `min m < min L(m)`
                            written inline; Corollary_e tries the condition on examples

Exact file-level imports (within the project):

| file             | imports                              |
|------------------|--------------------------------------|
| `Fundamentals_t` | —                                    |
| `Segment_t`      | `Fundamentals_t`                     |
| `Segment_u`      | `Segment_t`                          |
| `Basic_t`        | `Segment_t`, `Segment_u`             |
| `Basic_u`        | `Segment_u`, `Basic_t`               |
| `Basic_e`        | `Basic_t`, `Basic_u`                 |
| `Ladder1_t`      | `Basic_t`, `Basic_u`                 |
| `Ladder1_u`      | `Basic_u`, `Ladder1_t`               |
| `Ladder1_e`      | `Basic_t`, `Ladder1_t`, `Ladder1_u`  |
| `Ladder2_t`      | `Ladder1_t`, `Ladder1_u`             |
| `Ladder2_u`      | `Ladder1_u`, `Ladder2_t`             |
| `Ladder2_e`      | `Basic_t`, `Ladder1_t`, `Ladder2_t`, `Ladder2_u` |
| `RSK1_t`         | `Ladder2_t`, `Ladder2_u`             |
| `RSK1_u`         | `Ladder2_u`, `RSK1_t`                |
| `RSK1_e`         | `Basic_t`, `Ladder2_t`, `RSK1_t`, `RSK1_u` |
| `RSK2_t`         | `RSK1_t`, `RSK1_u`                   |
| `RSK2_u`         | `RSK1_u`, `RSK2_t`                   |
| `RSK2_e`         | `Basic_t`, `Ladder2_t`, `RSK1_t`, `RSK2_t`, `RSK2_u` |
| `RSK3_t`         | `RSK2_t`, `RSK2_u`                   |
| `RSK3_u`         | `RSK2_u`, `RSK3_t`                   |
| `RSK3_e`         | `Basic_t`, `Ladder1_t`, `Ladder2_t`, `RSK3_t`, `RSK3_u` |
| `MW1_t`          | `Basic_t`, `Basic_u`                 |
| `MW1_u`          | `Basic_u`, `MW1_t`                   |
| `MW1_e`          | `Basic_t`, `Basic_u`, `MW1_t`, `MW1_u` |
| `MW2_t`          | `MW1_t`, `MW1_u`                     |
| `MW2_u`          | `MW1_u`, `MW2_t`                     |
| `MW2_e`          | `Basic_t`, `Basic_u`, `MW1_t`, `MW1_u`, `MW2_t`, `MW2_u` |
| `Lemmas_u`       | `RSK3_u`, `MW2_u`                    |
| `Corollary_t`    | `Lemmas_u`                           |
| `Corollary_e`    | `Basic_t`, `RSK3_t`, `RSK3_u`        |

`LeanProof/lean` is a legacy self-contained prototype; it is not imported
by the root module.

## Building and checking

```sh
lake build                      # elaborates the entire development, evals included
```

To re-certify the main theorem is sorry-free, check its axioms:

```lean
import LeanProof.Corollary_t
#print axioms corollary_3_4     -- [propext, Classical.choice, Quot.sound]
```

## Tooling

Ships a `lean-beam` agent skill (`.claude/skills/lean-beam`) for fast,
build-free Lean proof iteration: cheap speculative checks against the proof
engine and zero-build module checkpoints instead of full rebuilds.

## The trusted text

The `_t` files of the project, complete, in dependency order: everything a reader checks
against the paper (the language layer `Fundamentals_t` is not repeated here). The `_u` files
add only proofs, the `_e` files only examples. Copied from the files on 2026-11-16; to
refresh, delete from this heading down and run

```sh
for f in Segment Basic Ladder1 Ladder2 RSK1 RSK2 RSK3 MW1 MW2 Corollary; do
  printf '\n### `%s_t.lean`\n\n```lean\n' $f; cat LeanProof/${f}_t.lean; printf '```\n'; done >> README.md
```





### `Segment_t.lean`

```lean
import Mathlib.Order.Interval.Basic
import Mathlib.Algebra.Order.Group.Int
import LeanProof.Fundamentals_t

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false

/-! # Segments (trusted definitions)

A segment `[a, b]` is a nonempty interval of integers. Its order, and everything built on
segments, is in `Basic_t`; what `auto_prop` needs to know about segments first is in `Segment_u`. -/

def Segment := NonemptyInterval ℤ

def Segment.a (s : Segment) : ℤ := s.fst
def Segment.b (s : Segment) : ℤ := s.snd

/-- `Segment a b` is the segment `[a, b]`; the proof of `a ≤ b` is found automatically. -/
macro_rules | `(Segment $a:term $b:term) => `(id (α := Segment) ⟨⟨$a, $b⟩, by auto_prop⟩)
```

### `Basic_t.lean`

```lean
import Mathlib.Order.Interval.Lex
import Mathlib.Data.List.Sublists
import Mathlib.Data.Set.Lattice
import Mathlib.Data.List.Pairwise
import Mathlib.Logic.Relation
import Mathlib.Order.Interval.Basic
import Mathlib.Algebra.Order.Group.Int
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
```

### `Ladder1_t.lean`

```lean
import LeanProof.Basic_t
import LeanProof.Basic_u
import Mathlib.Data.Set.Defs

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false

/-- d(Δ) = max{j : ∃ i₀ = Δ, i₁, …, iⱼ ∈ I such that Δ_{iᵣ} ≪ Δ_{iᵣ₊₁}, r = 0, …, j − 1} -/
def depthSet (m : Multisegment) (s : Segment) : Set ℕ :=
  { j | ∃ i : Indices (j + 1) m,
        m.segments[i.val[0]] = s ∧
        ∀ r (_ : r < j), m.segments[i.val[r]] ≪ m.segments[i.val[r + 1]] }
```

### `Ladder2_t.lean`

```lean
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
    (∀ n : Fin m.segments.length, (n ∈ i ↔ depth_of_segment m m.segments[n] = k)) ∧
    -- Δ_{i₀} ⊃ … ⊃ Δ_{i_l}
    (∀ r : ℕ, r + 1 < l → m.segments[i[r + 1]] ⊆ m.segments[i[r]]) }
```

### `RSK1_t.lean`

```lean
import LeanProof.Ladder2_t
import LeanProof.Ladder2_u
import Mathlib.Data.List.Lex

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false

/-! # RSK, part 1: the fibers (trusted definitions)

Paper, §2: "For any `k = 0, …, d` choose an admissible enumeration of `𝔡⁻¹(k)`". -/

/-- `Δ_{i^k_0} ⊇ … ⊇ Δ_{i^k_l}`: the segments of `𝔡⁻¹(k)` in the order of an admissible
enumeration (any one: they all list the same segments). -/
def fiber (m : Multisegment) (k : ℕ) : List Segment :=
  let i ∈ admissibleEnumerations m k; [m.segments[j] | j ∈ i]
```

### `RSK2_t.lean`

```lean
import LeanProof.RSK1_t
import LeanProof.RSK1_u

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false

/-! # RSK, part 2: the rung of a fiber (trusted definitions) -/

/-- The rung of a nonempty fiber `𝔡⁻¹(d)` (paper (2.2)): the largest begin point paired with
the largest end point. -/
def bucketRung (m : Multisegment) (d : ℕ) (h : fiber m d ≠ []) : Segment :=
  Segment (maximum {(x.a) | x ∈ fiber m d}) (maximum {(x.b) | x ∈ fiber m d})
```

### `RSK3_t.lean`

```lean
import LeanProof.RSK2_t
import LeanProof.RSK2_u
import Mathlib.Data.List.Sort

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.hashCommand false

/-! # RSK algorithm — single step (trusted definitions)

One step of the RSK / MW algorithm: given a multisegment `m`, produce the
maximal ladder rungs and the residual multisegment.

Each bucket's rung is the coordinatewise max of its segments (`bucketRung`);
`ladderRungs` is the set of them. The residual replaces each neighbouring pair
`Δᵢ, Δᵢ₊₁` of a fiber by the derived segment `[Δᵢ.a, Δᵢ₊₁.b]`. The correctness
lemmas (`ladderRungs_isLadder`, Lemma 2.2, Corollary 2.3) live in `RSK3_u`. -/

/-- `d(m) = max_{i ∈ I} 𝔡(i)`, the depth of a nonzero multisegment. -/
def maxDepth (m : Multisegment) (h : m.segments ≠ []) : ℕ :=
  maximum {depth_of_segment m s | s ∈ m.segments}

/-- `𝔩(m)`: the rungs of all nonempty fibers. -/
def ladderRungs (m : Multisegment) : Set Segment :=
  {bucketRung m d | (d : ℕ) (_ : fiber m d ≠ [])}

/-- Paper (2.1a): `Δ'_i = [b(Δ_i), e(Δ_{i^∨})]` where `Δ_{i^∨} = Δ_{i+1}` is
the next segment of the fiber `𝔡⁻¹(d)` (in the order of our enumeration). -/
def bucketResidual (m : Multisegment) (d : ℕ) : List Segment :=
  [Segment (fiber m d)[i].a (fiber m d)[i + 1].b | i < (fiber m d).length - 1]

-- /-- `i^\vee`: the nesting successor of `s` in bucket `d` (the next, more-inner segment in
-- admissible order); `none` if `s` is the innermost element. -/
-- def bucketSucc (m : Multisegment) (d : ℕ) (s : Segment) : Option Segment :=
--   let l := (bucket m d).map (·.val)
--   ((l.zip l.tail).find? (fun p => decide (p.1 = s))).map (·.2)

/-- `m′ = Σ_{i ∈ I′′} Δ'_i` (paper (2.1c)): all the derived segments, of all fibers. -/
def residual (m : Multisegment) (h : m.segments ≠ []) : Multisegment :=
  [s | k ≤ maxDepth m, s ∈ bucketResidual m k]

/-- **One step of the RSK algorithm** on a nonzero multisegment: the extracted ladder and
the residual. -/
def rsk_step (m : Multisegment) (h : m.segments ≠ []) : Set Segment × Multisegment :=
  (ladderRungs m, residual m)
```

### `MW1_t.lean`

```lean
import LeanProof.Basic_t
import LeanProof.Basic_u
import Mathlib.Data.List.Chain

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false

/-!
# Mœglin–Waldspurger, part 1: leading indices (trusted definitions)

Paper §MW: the leading indices `i₁, …, i_k` of a multisegment `m`.
-/

abbrev chainLink (s₁ s₂ : Segment) : Prop := s₁ ≪ s₂ ∧ s₂.a = s₁.a + 1

/-- A chain `Δ₁, …, Δₖ`: each segment strictly precedes the next, which begins one step later. -/
abbrev isChain (segments : List Segment) : Prop :=
  ∀ i, i + 1 < segments.length → chainLink segments[i] segments[i + 1]

def Chain := {ms : Multisegment // isChain ms.segments}

def segmentResidual (s : Segment) (h : s.a < s.b) : Segment :=
  Segment (s.a + 1) s.b

abbrev isFirst (m : Multisegment) (s : Segment) : Prop :=
  s ∈ m.segments ∧ ∀ t ∈ m.segments, s ≤ t

abbrev isNext (m : Multisegment) (s t : Segment) : Prop :=
  t ∈ m.segments ∧ chainLink s t ∧ ∀ u ∈ m.segments, chainLink s u → t ≤ u

abbrev isLast (m : Multisegment) (s : Segment) : Prop :=
  ∀ t ∈ m.segments, ¬ chainLink s t

def leadingIndices (m : Multisegment) : Set (List ℕ) :=
  { i : List ℕ | ∃ k : {k : ℕ // i ∈ Indices k m ∧ 0 < k},
        isFirst m m.segments[i[0]] ∧
        (∀ j : ℕ, j + 1 < k → isNext m m.segments[i[j]] m.segments[i[j + 1]]) ∧
        (∀ j : ℕ, j + 1 = k → isLast m m.segments[i[j]]) }
```

### `MW2_t.lean`

```lean
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

def makeResidual (m : Multisegment) (h : m.segments ≠ []) : Multisegment :=
  let i ∈ leadingIndices m;
  [m.segments[j] | j < m.segments.length, j ∉ i]
    ++ [segmentResidual m.segments[j] | j ∈ i, m.segments[j].a < m.segments[j].b]

def deltaCirc (m : Multisegment) (h : m.segments ≠ []) : Segment :=
  let i ∈ leadingIndices m; Segment m.segments[i[0]].a m.segments[i[i.length - 1]].a

def mw_step (m : Multisegment) (h : m.segments ≠ []) : Segment × Multisegment :=
  (deltaCirc m, makeResidual m)
```

### `Corollary_t.lean`

```lean
import LeanProof.Lemmas_u

seal maximum anyOf in
/-- **Corollary 3.4** (paper Cor. `main`): `(K × Id)(MW(m)) = (Id × MW)(K(m))` for
`min m < min L(m)` — one MW step followed by one RSK step yields the same data as one
RSK step followed by one MW step. Both sides are the triple
(extracted ladder, remaining multisegment, MW segment):
* left — `MW` first: the ladder and remainder of `m†`, with `Δ°(m)`;
* right — `K` first: the ladder of `m`, with the MW step of `m′`.
Assembled from `mw_preserves_ladder`, `mw_residual_commute` and
`deltaCirc_eq_of_residual` (`Lemmas_u`). -/
theorem corollary_3_4
    (m : Multisegment) (hm : m.segments ≠ [])
    (h_min : m.segments[0].a < (sorted (ladderRungs m))[0].a) :
    let KId_MW : Set Segment × Multisegment × Segment :=
      ((rsk_step (mw_step m hm).2).1,
       (rsk_step (mw_step m hm).2).2,
       (mw_step m hm).1)
    let IdMW_K : Set Segment × Multisegment × Segment :=
      ((rsk_step m).1,
       (mw_step (rsk_step m).2).2,
       (mw_step (rsk_step m).2).1)
    KId_MW = IdMW_K := by
  intro KId_MW IdMW_K
  have h := min_m_lt_min_lm_of_index m hm h_min
  exact congrArg₂ Prod.mk (mw_preserves_ladder m hm h).symm
    (congrArg₂ Prod.mk (mw_residual_commute m hm h) (deltaCirc_eq_of_residual m hm h))
```
