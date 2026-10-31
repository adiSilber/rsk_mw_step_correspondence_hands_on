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

- a part's `_t` file may depend only on files of **earlier** (lower-level)
  parts — including their `_u` files;
- a part's `_u` file may depend on the `_t` and `_u` files of its **own** part
  and of earlier ones;
- a part's `_e` file may depend on the `_t` and `_u` files of its **own** part
  and of earlier ones (e.g. `Basic_e` uses `Basic_u`'s decidability
  instances, and `MW1_e` uses `MW1_u` to demonstrate the greedy scan). Nothing
  imports an `_e` file, so this adds nothing to the trusted surface.

Definitions in a `_u` file are `private`, unless a later `_u` file needs them. Such a
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
               `maximum`, `first` and `sorted` of a finite set, `let x ∈ S; e` (an arbitrary
               element, when `e` does not depend on it), list comprehensions `[x ∈ l | p]`
               and `[f | x ∈ l, (y, z) ∈ l', k ≤ n, p, …]` (a bare `p` keeps the choices
               satisfying it; a fact `f` needs and the binders do not give becomes a
               condition too),
               lists usable as sets, `p → q` keeps `p` in scope for `q`,
               `x ∈ s` converts `x` to the element type of `s`; below everything
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
    └── MW2    leadingChain, makeResidual (m^MW), deltaCirc (Δ^MW), mw_step, by the paper's
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

| file             | imports                                                        |
|------------------|----------------------------------------------------------------|
| `Fundamentals_t` | —                                                              |
| `Segment_t`      | `Fundamentals_t`                                               |
| `Segment_u`      | `Segment_t`                                                    |
| `Basic_t`        | `Fundamentals_t`, `Segment_t`, `Segment_u`                     |
| `Basic_u`        | `Basic_t`                                                      |
| `Basic_e`        | `Basic_t`, `Basic_u`                                           |
| `Ladder1_t`      | `Fundamentals_t`, `Basic_t`, `Basic_u`                         |
| `Ladder1_u`      | `Basic_t`, `Basic_u`, `Ladder1_t`                              |
| `Ladder1_e`      | `Basic_t`, `Ladder1_t`, `Ladder1_u`                            |
| `Ladder2_t`      | `Basic_t`, `Basic_u`, `Ladder1_t`, `Ladder1_u`                 |
| `Ladder2_u`      | the above + `Ladder2_t`                                        |
| `Ladder2_e`      | `Basic_t`, `Ladder1_t`, `Ladder2_t`, `Ladder2_u`               |
| `RSK1_t`         | `Basic_t`, `Basic_u`, `Ladder1_t`, `Ladder1_u`, `Ladder2_t`, `Ladder2_u` |
| `RSK1_u`         | the above + `RSK1_t`                                           |
| `RSK1_e`         | `Basic_t`, `Ladder2_t`, `RSK1_t`, `RSK1_u`                     |
| `RSK2_t`         | the imports of `RSK1_t` + `RSK1_t`, `RSK1_u`                   |
| `RSK2_u`         | the above + `RSK2_t`                                           |
| `RSK2_e`         | `Basic_t`, `Ladder2_t`, `RSK1_t`, `RSK2_t`, `RSK2_u`           |
| `RSK3_t`          | the imports of `RSK2_t` + `RSK2_t`, `RSK2_u`                   |
| `RSK3_u`          | the above + `RSK3_t`                                            |
| `RSK3_e`          | `Basic_t`, `Ladder1_t`, `Ladder2_t`, `RSK3_t`, `RSK3_u`          |
| `MW1_t`          | `Basic_t`, `Basic_u`                                           |
| `MW1_u`          | `Basic_t`, `Basic_u`, `MW1_t`                                  |
| `MW1_e`          | `Basic_t`, `Basic_u`, `MW1_t`, `MW1_u`                         |
| `MW2_t`          | `Basic_t`, `Basic_u`, `MW1_t`, `MW1_u`                         |
| `MW2_u`          | the above + `MW2_t`                                            |
| `MW2_e`          | `Basic_t`, `Basic_u`, `MW1_t`, `MW1_u`, `MW2_t`, `MW2_u`       |
| `Lemmas_u`       | everything above it                                            |
| `Corollary_t`    | `Lemmas_u`                                                     |
| `Corollary_e`    | `Basic_t`, `RSK3_t`, `RSK3_u`                                  |

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
