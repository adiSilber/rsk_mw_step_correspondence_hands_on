# Essentials

The big issues our way of writing Lean is meant to solve. One line each; details live in
the code. (Maintained by hand; `README.md` describes the files, this describes the ideas.)

1. **Trust is layered.** `_t` files hold definitions a mathematician checks against the
   paper; `_u` files hold proofs and algorithms; `_e` files run every `_t` definition on
   examples. Nothing in `_t` is justified by anything in `_u`, except facts imported from
   an *earlier* stage.

2. **Trusted definitions read like the paper.** Set and list comprehensions (with conditions:
   `[f | j ∈ i, p]`), `maximum`, `sorted`, `let i ∈ S; …`, `m.segments[i]`,
   `∀ j, j + 1 < k → …`. No `match`, `if`, `filter`, `foldl`, `zip`, `erase`, `Option`,
   `insertionSort`, `head`, `↑`, named proof binders, or inline `by` proofs.

3. **Proof obligations are invisible.** Omitted proof arguments and index bounds are found
   by `auto_prop`; what it knows is taught in `_u` files, never written in `_t`.

4. **The language is separate from the project.** `Fundamentals_t` is the project-independent
   part (comprehensions, `maximum`/`first`/`sorted`, the proof-filling rules) and should be
   reusable elsewhere; project notions go to `Basic` and later stages.

5. **When a definition needs a fact, split the stage.** The fact is proved in a `_u` file
   between two `_t` files (Ladder1/2, RSK1/2/3, MW1/2); it is never proved inline.

6. **Choices are stated, not computed.** "Let `i` be a sequence of leading indices": the
   trusted text states the conditions (paper's (a)–(c)) and writes `let i ∈ leadingIndices m; …`,
   which Lean accepts only with a proof that the result does not depend on the choice; the
   algorithm that finds one (greedy scan) lives in `_u`. Likewise `fiber` is
   `let i ∈ admissibleEnumerations m k; …`.

7. **Say it explicitly.** `∀ t ∈ m.segments, s ≤ t`, not `IsLeast m.segments s`: a Mathlib
   name may hide a parameter (here, which order). *Open:* `Nodup`, `Pairwise`, `IsChain`,
   `<+` are still used — acceptable because their meaning is clear from the name, or to be
   spelled out too?

8. **Formulas are `abbrev`, objects are `def`.** A Prop-valued definition is shorthand for
   its formula (and decidable for free); a type, number, list or step is a new object.

9. **A multisegment is a sorted list,** so that `=` is equality of formal sums; every list of
   segments is a multisegment through a coercion, and `l₁ + l₂` is the formal sum of two lists
   (both in `Basic_u`).

10. **Hypotheses follow the paper.** `maxDepth`, `residual`, `rsk_step`, `mw_step` take
    `m.segments ≠ []` (the paper's `m ≠ 0`); no `0 ::` or empty-case conventions.

11. **Deliberate deviations are recorded.** The ladder is listed deepest-first (not the
    paper's order); the MW step is the mirror image, as in the paper's §MW.
