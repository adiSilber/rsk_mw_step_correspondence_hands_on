# Ideas for later

Things we decided not to do yet, but would like to make better.

## `Fundamentals_t`

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
