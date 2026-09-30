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
  instances, and `MW_e` uses `MW_u` to demonstrate `leadingChain`). Nothing
  imports an `_e` file, so this adds nothing to the trusted surface.

Every definition in a `_u` file is `private`, so no lemma statement outside
that file can depend on it — with one sanctioned exception, `MW.leadingChain`
(public in `MW_u`; it is the object the proposition layer reasons about, and it
appears in **no** trusted statement).

"Earlier" refers not to a single linear chain but to the dependency **tree**
below.

## Dependency tree

```
Fundamentals   project-wide macros (e.g. the index-validity rule for `l[i]`);
               below everything, imported where needed
Basic          segments (= NonemptyInterval ℤ), multisegments, ≪, ⊆, lex order,
               Indices (index lists into a multisegment)
├── Ladder1    depthSet (the paper's depth set, by set comprehension);
│   │          Ladder1_u proves it finite by computing it (depthFinset)
│   └── Ladder2   depth_of_segment (= max of depthSet), isLadder, bucket, Ladder
│       └── RSK   bucketRung, maxDepth, ladderRungs, bucketResidual, residual, rsk_step
└── MW         chainLink, isChain, extendChain.go, Chain, segmentResidual,
                makeResidual, mw_step
                (MW depends on Basic only — RSK and MW are independent)

RSK + MW ──► Propositions   min_m_lt_min_lm, cond_rsk_residual_nonempty,
                            and all proof machinery (Lemma 2.1/2.2 API,
                            Δ°-preservation, ladder preservation, the
                            derived-pair counting calculus and telescoping)
             └── Corollary  deltaCirc_eq_of_residual, mw_preserves_ladder,
                            mw_residual_commute, corollary_3_4
```

Exact file-level imports (within the project):

| file             | imports                                                        |
|------------------|----------------------------------------------------------------|
| `Fundamentals_t` | —                                                              |
| `Basic_t`        | —                                                              |
| `Basic_u`        | `Basic_t`                                                      |
| `Basic_e`        | `Basic_t`, `Basic_u`                                           |
| `Ladder1_t`      | `Fundamentals_t`, `Basic_t`, `Basic_u`                         |
| `Ladder1_u`      | `Basic_t`, `Basic_u`, `Ladder1_t`                              |
| `Ladder1_e`      | `Basic_t`, `Ladder1_t`, `Ladder1_u`                            |
| `Ladder2_t`      | `Basic_t`, `Basic_u`, `Ladder1_t`, `Ladder1_u`                 |
| `Ladder2_u`      | the above + `Ladder2_t`                                        |
| `Ladder2_e`      | `Basic_t`, `Ladder1_t`, `Ladder2_t`, `Ladder2_u`               |
| `RSK_t`          | `Basic_t`, `Basic_u`, `Ladder1_t`, `Ladder1_u`, `Ladder2_t`, `Ladder2_u` |
| `RSK_u`          | the above + `RSK_t`                                            |
| `RSK_e`          | `Basic_t`, `Ladder1_t`, `Ladder2_t`, `RSK_t`                   |
| `MW_t`           | `Basic_t`, `Basic_u`                                           |
| `MW_u`           | `Basic_t`, `Basic_u`, `MW_t`                                   |
| `MW_e`           | `Basic_t`, `Basic_u`, `MW_t`, `MW_u`                           |
| `Propositions_t` | `RSK_t`, `RSK_u`, `MW_t`                                       |
| `Propositions_u` | everything above it                                            |
| `Propositions_e` | `Propositions_t`                                               |
| `Corollary_t`    | `Propositions_t`, `Propositions_u`                             |

`LeanProof/RSK.lean` is a legacy self-contained prototype; it is not imported
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
