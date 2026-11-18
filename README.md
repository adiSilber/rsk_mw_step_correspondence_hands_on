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
               type), any other is refused; a power `x ^ k` is taken in the type of
               its base and converted afterwards (`n ^ s` with no such power converts
               the base to the exponent's type); half-lines `(a, ∞)`; big O `f =O g` as
               the argument tends to `+∞`; below everything
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

Under `tools/`, run by hand after `lake build`: `tools/UnusedRSK.lean` and `tools/UnusedHecke.lean`
list the declarations nothing needs in each project (ESSENTIALS rules 12 and 13; the analysis is
the module `tools/Unused.lean`, one project at a time, see the Hecke section), and
`tools/Fundamentals_test.lean` fixes what the language layer accepts, computes and refuses, to be
run after every Mathlib upgrade.

## The Hecke L-function statement (`Hecke/`)

A second statement on the same language layer: the quasi-Riemann hypothesis for the
finite-order Hecke L-functions of `ℚ(√-3)`, paper "The Quasi-Riemann Hypothesis: A Zero-Free
Half-Plane Re(s) > 7/8" (September 30, 2026), Theorem 1.1, first sentence. It restates the
challenge file `HeckeSevenEighths.lean` of the OpenAI mathematics repository
(`verification_projects/math/lean/ComparatorChallenges/`) in the rules of this repository. The
trusted definitions are **not** the original's word for word: they follow the rules and are to be
checked against the paper, not against the original file; there is no formal link to it. The
final statement, `LFunction_ne_zero_of_seven_eighths_lt_re` in `Hecke/Main_t.lean`, is left as
`sorry` exactly as in the challenge: the proof is the 21,000-line library of that repository and
is not the subject here. It is the only `sorry` in the repository.

Nothing here is computable (real and complex analysis), so the `_e` files exercise each trusted
definition by an `example` checked by `rfl`, `simp` or `norm_num`, the expected value written in
the statement, the closest thing to an `#eval`.

How the rules play out here, where they differ from the RSK part:

- **A theta pair is its data.** Mathlib's `WeakFEPair ℂ` bundles six pieces of data with seven
  proofs; the original proves them inside its definitions (46 lines of tactics). Here `PairData`
  is the six pieces, `PairData.Valid` the seven facts as one `Prop`-valued structure, and
  `WeakFEPair.ofData d` packs them; the facts are proved in `Theta1_u` and omitted where the pair
  is assembled, `auto_prop` finding them from `lattice_valid` (`grind ←`).
- **Sums read like the paper.** The sum over the classes is `∑ a, ∑ b, ∑ e, w a b * …`, not a sum
  over a product type with `p.1.1`, `p.1.2`, `p.2`.
- **Hypotheses last.** `pair N w (hN : 0 < N)`, `completed N w s (hN : 0 < N)`: callers never
  write them, as with `maxDepth m (h : m.segments ≠ [])`.
- **A Hecke character is the paper's residue character `ϕ`**: a nonzero modulus, a character of
  `O/𝔪` trivial on the six units, and a period `N ∈ 𝔪`; the L-function is "the lattice L-function
  divided by six", and the docstring says why six.
- **Deviations recorded.** (a) `Θ_ϕ` is reached as in the original, through products of two
  rescaled Hurwitz theta pairs per class and parity, because Mathlib proves the functional
  equation for those and nothing proves it for the paper's one-line lattice sum; the docstrings of
  `parity` and `lattice` state what is summed. (b) `ω` is Mathlib's chosen primitive cube root of
  unity, as in the original: `let ω ∈ {primitive cube roots of unity}; …` would need a proof that
  the L-function does not depend on the choice, which nothing in the library gives. (c) Casts are
  Lean's own (rule 14): a real power among complex factors, `d.ε * x ^ d.k * d.g x`, is the real
  power converted afterwards, by the layer's reading of `^`; the integers `x`, `y` enter `O` by
  type ascription, `(x : O)`. (d) The identification of the
  lattice sum with the Dirichlet series over ideals is not in the challenge, and so not here.
- **Open.** `Character1_u` declares one `instance`, that `F` is the cyclotomic extension of `ℚ`
  by the cube roots of unity, which the instance rule as written does not allow; it is a
  proposition, so any two proofs of it agree.

```
LeanProof.Fundamentals_t   the language layer; below everything
├── Pair_t        PairData (the six pieces of data of a theta pair), PairData.Valid (Mathlib's
│   │             seven facts), WeakFEPair.ofData (Mathlib's pair from data and facts),
│   │             WeakFEPair.data
│   ├── Pair_u      a Mathlib pair's data is valid
│   └── Theta1_t    product, rescale, even (Mathlib's Hurwitz pair as data), scaledEven,
│       │           rectangular, xShift, yShift, parity (one class, one parity), lattice (Θ_ϕ
│       │           as data: the weighted sum over the classes and parities)
│       ├── Theta1_u   every piece is valid; `lattice_valid` (what auto_prop needs in Theta2_t)
│       └── Theta2_t   pair (Mathlib's pair; facts omitted), completed (Mathlib's Λ),
│           │          latticeL = π^s Γ(s)⁻¹ Λ(s)
│           └── Theta_e    checks
└── Character1_t  F = ℚ(ζ₃) with its field structure, O = ℤ[ω] with its ring structure
    └── Character1_u  F is the cyclotomic extension by the cube roots of unity (what
        │             Character2_t needs)
        └── Character2_t  omega, coordinateElement (x + yω), HeckeCharacter (the residue
            │             character ϕ: modulus, character of O/𝔪, trivial on units, period),
            │             elementCoeff (ϕ(z)), coefficients (ϕ on classes modulo the period)
            ├── Character2_u  the period is positive (what auto_prop needs in Main_t)
            └── Character_e   checks (O is a domain, for them only; the trivial character)
                          (Theta and Character are independent)

Theta2_t + Character2_t + Character2_u ──► Main_t   continuedLattice, LFunction (÷ 6), the theorem
```

| file           | imports                                                             |
|----------------|---------------------------------------------------------------------|
| `Pair_t`       | `LeanProof.Fundamentals_t`, `Mathlib.NumberTheory.LSeries.AbstractFuncEq` |
| `Pair_u`       | `Pair_t`                                                            |
| `Theta1_t`     | `Pair_t`, `Mathlib.NumberTheory.LSeries.HurwitzZetaEven`            |
| `Theta1_u`     | `Theta1_t`, `Pair_u`                                                |
| `Theta2_t`     | `Theta1_t`, `Theta1_u`                                              |
| `Theta_e`      | `Theta2_t`                                                          |
| `Character1_t` | `LeanProof.Fundamentals_t`, `Mathlib.NumberTheory.NumberField.Cyclotomic.Basic` |
| `Character1_u` | `Character1_t`                                                      |
| `Character2_t` | `Character1_t`, `Character1_u`, `Mathlib.NumberTheory.MulChar.Basic` |
| `Character2_u` | `Character2_t`                                                      |
| `Character_e`  | `Character2_t`, `Character2_u`                                      |
| `Main_t`       | `Theta2_t`, `Character2_t`, `Character2_u`                          |

The trusted text is `Pair_t`, `Theta1_t`, `Theta2_t`, `Character1_t`, `Character2_t`, `Main_t`:
17 definitions, two structures, three instances and the theorem. What it makes explicit, which
the original leaves to the reader: what a theta pair is made of and which facts Mathlib demands
of it; what `parity` and `lattice` sum, in the paper's notation; that `Λ` is the paper's integral
`∫ (Θ_ϕ(v) − ϕ(0)) v^{s-1} dv` continued, with its two poles; that the L-function is the lattice
sum divided by six because each ideal has six generators; and that a `HeckeCharacter` is the
paper's residue character `ϕ`.

Ported on 2026-11-17 from a trial written on 2026-11-01 in the OpenAI repository under Lean 4.34
and a newer Mathlib; two Mathlib names differed and were replaced in `Theta1_u`. The two
libraries cannot be imported into one file: `residual` is a name of both `RSK3_t` and Mathlib's
topology, which the Hecke imports bring in; this is why the unused-declaration tool runs per
project.

## The trusted text

The `_t` files of both statements, complete, in dependency order: everything a reader checks
against the papers (the language layer `Fundamentals_t` is not repeated here). The `_u` files
add only proofs, the `_e` files only examples. Copied from the files on 2026-11-17; to
refresh, delete from the first `###` heading below and run

```sh
for f in Segment Basic Ladder1 Ladder2 RSK1 RSK2 RSK3 MW1 MW2 Corollary; do
  printf '\n### `%s_t.lean`\n\n```lean\n' $f; cat LeanProof/${f}_t.lean; printf '```\n'; done >> README.md
for f in Pair Theta1 Theta2 Character1 Character2 Main; do
  printf '\n### `Hecke/%s_t.lean`\n\n```lean\n' $f; cat Hecke/${f}_t.lean; printf '```\n'; done >> README.md
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

### `Hecke/Pair_t.lean`

```lean
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import LeanProof.Fundamentals_t

/-! # Functional-equation pairs (trusted definitions)

Mathlib's `WeakFEPair ℂ` is the device behind the meromorphic continuation: two functions `f`,
`g` on `(0, ∞)` with `f (1/x) = ε · x^k · g x`, each approaching a constant (`f₀`, `g₀`) faster
than every power at `∞`; its `Λ` is the Mellin transform of `f` with the two poles removed.
Mathlib bundles the six pieces of data with seven proofs. Here the data is a structure of its own,
the seven facts are one proposition, and `WeakFEPair.ofData` packs data and facts into Mathlib's
structure. The facts are proved in `_u` files and omitted where a pair is assembled (`Theta2_t`). -/

noncomputable section
open MeasureTheory

/-- The data of a functional-equation pair: `WeakFEPair ℂ` without its proofs. -/
structure PairData where
  /-- The function whose Mellin transform is studied. -/
  f : ℝ → ℂ
  /-- Its partner under `x ↦ 1/x`. -/
  g : ℝ → ℂ
  /-- The weight: `f (1/x) = ε · x^k · g x`. -/
  k : ℝ
  /-- The root number. -/
  ε : ℂ
  /-- The constant term of `f` at `∞`. -/
  f₀ : ℂ
  /-- The constant term of `g` at `∞`. -/
  g₀ : ℂ

/-- The seven facts Mathlib asks of the data, as it states them: `f` and `g` locally integrable on
`(0, ∞)`, `k > 0`, `ε ≠ 0`, the functional equation, and `f - f₀`, `g - g₀` smaller than every
power of `x` at `∞`. -/
structure PairData.Valid (d : PairData) : Prop where
  hf_int : LocallyIntegrableOn d.f (0, ∞)
  hg_int : LocallyIntegrableOn d.g (0, ∞)
  hk : 0 < d.k
  hε : d.ε ≠ 0
  h_feq : ∀ x ∈ (0, ∞), d.f (1 / x) = d.ε * x ^ d.k * d.g x
  hf_top : ∀ r : ℝ, (fun x ↦ d.f x - d.f₀) =O (fun x ↦ x ^ r)
  hg_top : ∀ r : ℝ, (fun x ↦ d.g x - d.g₀) =O (fun x ↦ x ^ r)

/-- Mathlib's pair, from data and its facts. -/
def WeakFEPair.ofData (d : PairData) (h : d.Valid) : WeakFEPair ℂ where
  f := d.f
  g := d.g
  k := d.k
  ε := d.ε
  f₀ := d.f₀
  g₀ := d.g₀
  hf_int := h.hf_int
  hg_int := h.hg_int
  hk := h.hk
  hε := h.hε
  h_feq := h.h_feq
  hf_top := h.hf_top
  hg_top := h.hg_top

/-- The data of a Mathlib pair. -/
def WeakFEPair.data (P : WeakFEPair ℂ) : PairData where
  f := P.f
  g := P.g
  k := P.k
  ε := P.ε
  f₀ := P.f₀
  g₀ := P.g₀

end
```

### `Hecke/Theta1_t.lean`

```lean
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Hecke.Pair_t

/-! # The lattice theta function (trusted definitions, stage 1)

Paper §4.4: "`6 π^{-s} Γ(s) L(s, ψ) = ∫₀^∞ (Θ_ϕ(v) − ϕ(0)) v^{s-1} dv`, `Θ_ϕ(v) = Σ_{a ∈ O} ϕ(a)
e^{-π v q_a}`", with `ϕ` periodic modulo the conductor and `q_a` the norm of `a`. The formalization
reaches `Θ_ϕ` through Mathlib's Hurwitz theta pairs: the sum over `a = x + yω ∈ O` with `(x, y)`
in one class modulo `N` splits, by the parity of `(y - b)/N`, into two products of two
one-variable theta functions with rectangular periods (`parity`), and `Θ_ϕ` is the weighted sum of
these over the classes (`lattice`). Everything here is data; that every piece is a valid pair is
proved in `Theta1_u`, and the Mathlib pair is assembled in `Theta2_t`. -/

noncomputable section

/-- The product of two pairs: functions multiply pointwise, weights add, root numbers and
constant terms multiply. -/
def product (P Q : PairData) : PairData where
  f v := P.f v * Q.f v
  g v := P.g v * Q.g v
  k := P.k + Q.k
  ε := P.ε * Q.ε
  f₀ := P.f₀ * Q.f₀
  g₀ := P.g₀ * Q.g₀

/-- Rescaling by `u`: `f` at `u·v`, `g` at `v/u`; the root number picks up `u^{-k}`. -/
def rescale (P : PairData) (u : ℝ) : PairData where
  f v := P.f (u * v)
  g v := P.g (u⁻¹ * v)
  k := P.k
  ε := P.ε * u ^ (-P.k)
  f₀ := P.f₀
  g₀ := P.g₀

/-- Mathlib's even Hurwitz theta pair at `a ∈ ℝ/ℤ`, as data: `f v = Σ_{n ∈ ℤ} e^{-π (n + a)² v}`,
`g v = Σ_{n ∈ ℤ} cos(2π n a) e^{-π n² v}`, weight `1/2`, root number `1`, `f₀ = [a = 0]`,
`g₀ = 1`. -/
def even (a : UnitAddCircle) : PairData := (HurwitzZeta.hurwitzEvenFEPair a).data

/-- The even pair at `a`, rescaled by `u`: `f v = Σ_n e^{-π (n + a)² u v}`. -/
def scaledEven (a : UnitAddCircle) (u : ℝ) : PairData := rescale (even a) u

/-- The theta data of a rectangular lattice: `f v = Σ_{m, n} e^{-π (u (m + a)² + v' (n + b)²) v}`;
weight `1/2 + 1/2 = 1`. -/
def rectangular (a b : UnitAddCircle) (u v' : ℝ) : PairData :=
  product (scaledEven a u) (scaledEven b v')

/-- The shifts placing the class `(a, b)` modulo `N` of `ℤ + ℤω`, with `(y - b)/N` of parity `e`,
on a rectangular lattice: `x = N(m + n) + a`, `y = b + N(2n + e)` give
`x² - xy + y² = N² (m + xShift)² + 3 N² (n + yShift)²`. -/
def xShift (a b N : ℝ) (e : Fin 2) : ℝ := (2 * a - b - N * e) / (2 * N)

/-- See `xShift`. -/
def yShift (b N : ℝ) (e : Fin 2) : ℝ := (b + N * e) / (2 * N)

/-- The theta data of the class `(a, b)` modulo `N` with parity `e`:
`f v = Σ e^{-π (x² - xy + y²) v}` over `x ≡ a`, `y ≡ b (mod N)`, `(y - b)/N ≡ e (mod 2)`; here
`x² - xy + y²` is the norm `q_{x + yω}`. -/
def parity (a b N : ℝ) (e : Fin 2) : PairData :=
  rectangular (xShift a b N e) (yShift b N e) (N ^ 2) (3 * N ^ 2)

/-- Paper §4.4, `Θ_ϕ(v) = Σ_{a ∈ O} ϕ(a) e^{-π v q_a}` for `ϕ` given on the classes modulo `N`:
the theta data of a weight `w` on `(ℤ/N)²`, the sum of the parity data of all classes, each
weighted by `w a b`. Weight `1`, root number `1`; `g` carries the root numbers of the parts. (The
class `(a, b)` enters `parity` by its representatives `0 ≤ a, b < N`, as real numbers.) -/
def lattice (N : ℕ) (w : Fin N → Fin N → ℂ) : PairData where
  f v := ∑ a, ∑ b, ∑ e, w a b * (parity a b N e).f v
  g v := ∑ a, ∑ b, ∑ e, w a b * (parity a b N e).ε * (parity a b N e).g v
  k := 1
  ε := 1
  f₀ := ∑ a, ∑ b, ∑ e, w a b * (parity a b N e).f₀
  g₀ := ∑ a, ∑ b, ∑ e, w a b * (parity a b N e).ε * (parity a b N e).g₀

end
```

### `Hecke/Theta2_t.lean`

```lean
import Hecke.Theta1_t
import Hecke.Theta1_u

/-! # The lattice L-function (trusted definitions, stage 2)

Paper §4.4: "`6 π^{-s} Γ(s) L(s, ψ) = ∫₀^∞ (Θ_ϕ(v) − ϕ(0)) v^{s-1} dv`". The theta data becomes a
Mathlib pair (its seven facts: `Theta1_u`), Mathlib's `Λ` is this integral continued to all of
`ℂ`, and the lattice L-function is `π^s Γ(s)⁻¹ Λ(s)`; the factor `6` comes in `Main_t`. -/

noncomputable section

/-- The theta pair of `w`, as Mathlib's structure. (Its seven facts are found by `auto_prop`, from
`lattice_valid` in `Theta1_u`; they need `N > 0`.) -/
def pair (N : ℕ) (w : Fin N → Fin N → ℂ) (hN : 0 < N) : WeakFEPair ℂ :=
  WeakFEPair.ofData (lattice N w)

/-- Mathlib's `Λ` of the pair: `∫₀^∞ (Θ(v) − Θ(∞)) v^{s-1} dv` for `Re s` large, continued to all
of `ℂ`, with poles at most at `s = 0` (residue `-f₀`) and `s = 1` (residue `ε g₀`). -/
def completed (N : ℕ) (w : Fin N → Fin N → ℂ) (s : ℂ) (hN : 0 < N) : ℂ := (pair N w).Λ s

/-- The lattice L-function: `π^s Γ(s)⁻¹ Λ(s)`, which for `Re s > 1` is
`Σ_{a ∈ O, a ≠ 0} ϕ(a) q_a^{-s}` with `ϕ` the weight read on classes. -/
def latticeL (N : ℕ) (w : Fin N → Fin N → ℂ) (s : ℂ) (hN : 0 < N) : ℂ :=
  Real.pi ^ s * (Complex.Gamma s)⁻¹ * completed N w s

end
```

### `Hecke/Character1_t.lean`

```lean
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import LeanProof.Fundamentals_t

/-! # The field (trusted definitions, stage 1)

Paper §1: "Let `F = ℚ(√-3)`, let `O` be its ring of integers". `F` is Mathlib's cyclotomic field
`ℚ(ζ₃)`, and it carries that field's structure (as `Segment` carries the order of `ℤ ×ₗ ℤ` in the
RSK/MW repository). Stage 2 (`Character2_t`) names `ω`, which needs two facts (`F` is a number
field, and the extension of `ℚ` by the cube roots of unity), stated in `Character1_u`. -/

noncomputable section

/-- The field `F = ℚ(√-3) = ℚ(ζ₃)`. -/
def F := CyclotomicField 3 ℚ

/-- `F` is a field, and an algebra over `ℚ`: the structure of the cyclotomic field. -/
instance : Field F := inferInstanceAs (Field (CyclotomicField 3 ℚ))
instance : Algebra ℚ F := inferInstanceAs (Algebra ℚ (CyclotomicField 3 ℚ))

/-- Its ring of integers `O = ℤ[ω]`. -/
def O := NumberField.RingOfIntegers F

/-- `O` is a commutative ring: the structure of the ring of integers. -/
instance : CommRing O := inferInstanceAs (CommRing (NumberField.RingOfIntegers F))

end
```

### `Hecke/Character2_t.lean`

```lean
import Mathlib.NumberTheory.MulChar.Basic
import Hecke.Character1_t
import Hecke.Character1_u

/-! # Finite-order Hecke characters (trusted definitions, stage 2)

Paper §1: "A finite-order Hecke character `η` modulo a nonzero integral ideal `f` is a character
of the ray class group modulo `f`, extended by zero to ideals not coprime to `f`." Paper §4.4:
"define the periodic residue character `ϕ(a) = ψ((a))` when `(a, f) = 1`, with value zero
otherwise. … `ϕ` is trivial on the six units because `(u) = (1)` for a unit." The challenge takes
`ϕ` as the primary object: a character of `O/𝔪` trivial on the units, read on the coordinates
`x + yω` modulo a period `N ∈ 𝔪`. -/

noncomputable section

/-- A primitive cube root of unity, as an integer of `F`: Mathlib's chosen `ζ₃`. -/
def omega : O := (IsCyclotomicExtension.zeta_spec 3 ℚ F).toInteger

/-- The integer `x + yω`. -/
def coordinateElement (x y : ℤ) : O := (x : O) + (y : O) * omega

/-- A finite-order Hecke character, as its residue character `ϕ`: a nonzero modulus `𝔪`, a
multiplicative character of `O/𝔪` with values in `ℂ`, trivial on the units of `O`, and a period
`N > 0` with `N ∈ 𝔪`, so that `ϕ(x + yω)` depends on `x`, `y` modulo `N` only. -/
structure HeckeCharacter where
  modulus : Ideal O
  modulus_ne_bot : modulus ≠ ⊥
  residue : MulChar (O ⧸ modulus) ℂ
  unit_trivial : ∀ u : Oˣ, residue (Ideal.Quotient.mk modulus (u : O)) = 1
  period : ℕ
  period_pos : 0 < period
  period_mem : (period : O) ∈ modulus

/-- `ϕ(z)`: the residue character at `z mod 𝔪`. -/
def elementCoeff (χ : HeckeCharacter) (z : O) : ℂ := χ.residue (Ideal.Quotient.mk χ.modulus z)

/-- `ϕ` on the classes modulo `N`: its value at `a + bω`, `0 ≤ a, b < N`. -/
def coefficients (χ : HeckeCharacter) (a b : Fin χ.period) : ℂ :=
  elementCoeff χ (coordinateElement a b)

end
```

### `Hecke/Main_t.lean`

```lean
import Hecke.Theta2_t
import Hecke.Character2_t
import Hecke.Character2_u

/-! # The statement (trusted)

Paper Theorem 1.1: "Every finite-order Hecke L-function over `F = ℚ(√-3)` has no zero in
`Re s > 7/8`. … A pole at `s = 1` for a principal character is allowed." Scope note
`docs/003.md`. The L-function is the lattice L-function of `ϕ`, read on coordinates modulo the
period, divided by six: paper §4.4, "The factor six counts the generators of each ideal." -/

noncomputable section

/-- The lattice L-function of `ϕ`: `Σ_{a ∈ O, a ≠ 0} ϕ(a) q_a^{-s}`, continued. (That the period
is positive is found by `auto_prop`, from `Character2_u`.) -/
def continuedLattice (χ : HeckeCharacter) (s : ℂ) : ℂ := latticeL χ.period (coefficients χ) s

/-- The Hecke L-function `L(s, η) = Σ_{𝔞 ≠ 0} η(𝔞) (N𝔞)^{-s}`, continued: each nonzero ideal has
six generators. (That the lattice sum is the sum over ideals is proved in the proof library,
`OAI/NumberTheory/DirichletL/Hecke/IdealBridge.lean`, not in the challenge.) -/
def LFunction (χ : HeckeCharacter) (s : ℂ) : ℂ := continuedLattice χ s / 6

/-- **Theorem 1.1.** `L(s, χ) ≠ 0` for `Re s > 7/8`, except at `s = 1` for the trivial
character. -/
theorem LFunction_ne_zero_of_seven_eighths_lt_re
    (χ : HeckeCharacter) {s : ℂ} (hs : (7 / 8 : ℝ) < s.re)
    (hpole : ¬ (χ.residue = 1 ∧ s = 1)) : LFunction χ s ≠ 0 := by sorry

end
```
