# Ideas for later

Things we decided not to do yet, but would like to make better.

## `Fundamentals_t`

- **Binder capture in `[f | …, k < n, …]` — a meaning bug in trusted code** (2026-10-31). An
  identifier before `<`, `≤` or `∈` in a comprehension always opens a new variable, even when
  one of that name is in scope: `def test (i : ℕ) : List ℕ := [i | i < 3]` gives `[0, 1, 2]`
  for every `i`, where a reader sees "`[i]` if `i < 3`". Lean is still sound; the `_t`
  contract is not: a theorem about it would be a true theorem about the wrong object. Only an
  unused-variable warning, and none if the outer `i` is used elsewhere. The six comprehension
  sites in this project were checked (2026-10-31): no capture. Fix: the comprehension must
  refuse an identifier that is already in scope — a macro cannot see the scope, an `elab` can.
- **`f a` is read as a value where plain Lean reads a function** (2026-10-31). With
  `f (n : ℕ) (_ : 0 < n) : ℕ`, `def g := f 1` gives `g : ℕ`; plain Lean gives
  `g : 0 < 1 → ℕ`. The two readings differ silently only where nothing fixes the type
  (a `let`, a pair, a list element); elsewhere one of them errors. Someone who knows the
  signature of `f` expects our reading, but it is a departure from Lean, and it should be stated
  in the README's description of the rule, or the rule should not fill when no type is
  expected and the term is a function after filling.
- **A type applied to arguments builds an element of it.** Today `Segment a b` works only
  through a `Segment`-specific macro in `Basic_t`. A general rule would make *any* structure
  name usable that way: the arguments fill its data fields in order, and its proof fields are
  found by `auto_prop`. Then the examples could read
  `Multisegment [Segment 1 3, Segment 2 4]` instead of
  `⟨[⟨⟨1, 3⟩, by omega⟩, ⟨⟨2, 4⟩, by omega⟩], by decide⟩`, and the macro in `Basic_t` goes
  away. A working prototype (about 30 lines, `@[term_elab app]`) was written on 2026-10-12:
  list the structure's fields flattened through parents, tag each as data or proof, and
  elaborate `{ field₁ := a, …, proofField := by auto_prop : T }`. It needs `decide` added to
  `auto_prop` for the sortedness of concrete lists. Not applied because it is the longest
  piece in `Fundamentals_t`.
- Automatically generated versions of `maximum` for other set functions (`minimum`, …).
- **`let x ∈ S; e` for sets without an order** (2026-10-31). `anyOf` evaluates `e` at
  `first S`, so it asks for `[LinearOrder α]` and `[Fintype S]`, which the mathematics does not
  need (only `S` nonempty and `e` constant on `S`, the two proofs it demands). In a project
  whose sets are of group elements, functions or points the line is rejected. The general
  definition is `f h.some h.some_mem` — noncomputable, so no `#eval` on anything built on it
  (here that would be 38 evals, everything from `fiber`, `leadingChain`, `makeResidual`,
  `deltaCirc` upward). Offer both under the same syntax: the computing one when the instances
  exist, the noncomputable twin otherwise.
- **`Decidable` in the comprehensions and in `auto_prop`** (2026-10-31). `[x ∈ l | p x]` and
  the condition binder `[f | …, p]` need an instance `Decidable p`; for `=` on `ℝ`, continuity,
  and the like there is none, and the definition fails with "failed to synthesize Decidable".
  Such a project needs `open Classical` in its `_t` file and `noncomputable` on those
  definitions — correct, but worth saying in the README. Also `auto_prop` tries `decide` before
  `grind`; on a closed goal with large numbers (`Nat.Prime 1000003`, `∀ i < 10 ^ 6, …`) `decide`
  can run for minutes before `grind` is tried. Consider a heartbeat bound on the `decide` step,
  or `grind` first.

## `_u` files

- **`Fintype` instances in `_u` files — to be checked** (2026-10-23). `Ladder1_u` (`depthSet`),
  `Ladder2_u` (`admissibleEnumerations`), `MW1_u` (`leadingIndices`), `RSK2_u` and `RSK3_u` (the
  rungs). A `Decidable` instance is a yes/no procedure with a proof; a `Fintype` instance is more:
  a computed list of the elements with a proof that it is complete. Any two such instances agree,
  so they should not be able to change what a `_t` term means, but this has not been looked at
  carefully: check that no `_t` definition depends on which list is computed, and that the lists
  the `_e` files print are the intended ones.
- **How to deal with dangerous instances.** Some instances give a `_t` term its meaning rather
  than a way to compute it: the reading of a list as a multisegment (`Coe`), the order on
  segments (`LinearOrder`), a `+` if we ever had one again, `Repr` for printing. Such an
  instance in a `_u` file would change what `_t` text means. Today the rule is informal: those
  live in `_t` (or `Segment_u` for `Repr`), and a `_u` file may contain an instance only of a
  class whose instances are all equal (`Decidable`, `Fintype`). Think about how to make this
  checkable — a list of allowed classes, a linter, or a convention a reader can verify at a
  glance — and whether `Repr` in a `_u` file is really harmless.

## `Basic_t`

- `open scoped List` is there only for `<+` in `subms`; writing `ms₀.segments.Sublist
  ms₁.segments` would make the file self-explanatory and the `open` line unnecessary.

## `MW1_t`

- `isChain` and `Chain` feel like extra stuff: `mw_step` uses neither (`extendChain.go` tests
  `chainLink` directly); `isChain` exists only to define `Chain`, and `Chain` is used only inside
  `MW1_u`. Options: keep `Chain` with the formula inline
  (`{ms : Multisegment // ms.segments.IsChain chainLink}`) and drop `isChain`, or move both to
  `MW1_u` so `MW1_t` keeps just `chainLink` and the paper's conditions.
