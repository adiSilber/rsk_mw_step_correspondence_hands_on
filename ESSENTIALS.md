# Essentials

The big issues our way of writing Lean is meant to solve. One line each; details live in
the code. (Maintained by hand; `README.md` describes the files, this describes the ideas.)

1. **Trust is layered.** `_t` files hold definitions a mathematician checks against the
   paper; `_u` files hold proofs and algorithms; `_e` files run every `_t` definition on
   examples. Nothing in `_t` is justified by anything in `_u`, except facts imported from
   an *earlier* stage.

2. **Trusted definitions read like the paper.** Set and list comprehensions (with conditions:
   `[f | j ∈ i, p]`), `maximum`, `sorted`, `let i ∈ S; …`, `m.segments[i]`,
   `∀ j, j + 1 < k → …`. A partial notion takes its condition as a hypothesis
   (`segmentResidual s (h : s.a < s.b)`, `maxDepth m (h : m.segments ≠ [])`), which callers
   never write; a comprehension over such a notion names the condition as a binder
   (`[segmentResidual m.segments[j] | j ∈ i, m.segments[j].a < m.segments[j].b]`), and inside
   the comprehension that binder is the hypothesis the notion asks for. No `match`, `filter`,
   `foldl`, `zip`, `erase`, `Option`, `insertionSort`, `head`, `↑`, or inline `by` proofs.

3. **Proof obligations are invisible.** Omitted proof arguments and index bounds are found
   by `auto_prop`; what it knows is taught in `_u` files, never written in `_t`
   (`Fundamentals_t` teaches only the facts about its own constructs).

4. **The language is separate from the project.** `Fundamentals_t` is the project-independent
   part (comprehensions, `maximum`/`sorted`, the proof-filling rules) and should be
   reusable elsewhere; project notions go to `Basic` and later stages.

5. **When a definition needs a fact, split the stage.** The fact is proved in a `_u` file
   between two `_t` files (Ladder1/2, RSK1/2/3, MW1/2); it is never proved inline.

6. **Choices are stated, not computed.** "Let `i` be a sequence of leading indices": the
   trusted text states the conditions (paper's (a)–(c)) and writes `let i ∈ leadingIndices m; …`,
   which Lean accepts only with a proof that the result does not depend on the choice; the
   algorithm that finds one (greedy scan) lives in `_u`. Likewise `fiber` is
   `let i ∈ admissibleEnumerations m k; …`. The same independence proof is what lets the
   definition compute: the element is taken from the finite enumeration of the set, so no
   order on the elements is needed and nothing is noncomputable.

7. **Say it explicitly.** `∀ t ∈ m.segments, s ≤ t`, not `IsLeast m.segments s`: a Mathlib
   name may hide a parameter (here, which order). *Open:* `Nodup`, `Pairwise`, `IsChain`,
   `<+` are still used — acceptable because their meaning is clear from the name, or to be
   spelled out too?

8. **Formulas are `abbrev`, objects are `def`.** A Prop-valued definition is shorthand for
   its formula (and decidable for free); a type, number, list or step is a new object.

9. **A multisegment is a sorted list,** so that `=` is equality of formal sums. Every list of
   segments is a multisegment through a coercion (`Basic_t`: increasing order, repeats kept),
   and `l₁ ++ l₂` is the formal sum of two lists.

10. **Hypotheses follow the paper.** `maxDepth`, `residual`, `rsk_step`, `mw_step` take
    `m.segments ≠ []` (the paper's `m ≠ 0`); no `0 ::` or empty-case conventions.

11. **Deliberate deviations are recorded.** None at present: the ladder is a set, as in the
    paper, and the MW step follows the paper's §MW (itself the mirror image of the classical
    algorithm).

12. **Nothing is kept that nothing needs.** Every declaration is used: by another declaration,
    by `corollary_3_4`, or by an `_e` eval; otherwise it is deleted. A `_t` definition the
    corollary never reaches is extra vocabulary and goes too (`leadingChain`, 2026-11-01).
    Claude checks this with `tools/Unused.lean`, a script that lists every constant of the
    project and what mentions it; the script itself has not been reviewed and should be. Two
    things leave no trace in it and are checked by hand: coercion instances, which are
    unfolded where they are written, and `rfl` lemmas, which `simp` applies without
    recording them.

13. **Private unless needed later.** A `_u` definition or lemma is `private` unless a later
    file names it; a public proof-side definition lives in `namespace Proof` and is written
    with its full name, which no `_t` or `_e` file ever does. Privacy is hygiene, not safety:
    a private lemma can be rewritten or deleted without looking elsewhere, a name clash
    between files is impossible, and a reader of a later file sees only what it may use.
    List C of `tools/Unused.lean` reports the public `_u` declarations only their own file
    mentions.

14. **A conversion never changes a value.** Lean inserts coercions on its own wherever the
    expected type is known, and the trusted text relies on that (no `↑` is written). They
    are safe when injective: `Fin k → ℕ`, subtype → base type, `ℕ`/`ℤ` into a type with
    `CharZero`. `x ∈ s` is the one place Lean would miss them; `Fundamentals_t` inserts them
    there itself and refuses any other conversion, so a number is never reduced modulo `k`
    and a list never loses its order unnoticed. A conversion that loses information is
    declared, never implicit (the list-to-multisegment coercion of `Basic_t`, rule 9).
