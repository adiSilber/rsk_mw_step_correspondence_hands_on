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

## `Basic_t`

- `open scoped List` is there only for `<+` in `subms`; writing `ms₀.segments.Sublist
  ms₁.segments` would make the file self-explanatory and the `open` line unnecessary.

## RSK

- `residual` still loops over `List.range (maxDepth m + 1)`; it should be stated like the
  paper, as the sum over all fibers of their derived segments.
