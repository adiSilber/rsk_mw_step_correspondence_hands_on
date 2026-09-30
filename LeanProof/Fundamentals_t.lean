import Mathlib.Tactic.Common

/-! Project-wide macros and notation, shared by many parts. Lowest file in the hierarchy. -/

/-- Discharges index-validity side goals of `l[i]` by `grind`. A definition whose unfolding
is needed is tagged `grind =` in a `_u` file (e.g. `Indices`, in `Basic_u`). -/
macro_rules
  | `(tactic| get_elem_tactic_extensible) => `(tactic| grind [List.getElem_mem])
