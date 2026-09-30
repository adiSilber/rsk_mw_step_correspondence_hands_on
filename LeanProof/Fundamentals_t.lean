import Mathlib.Tactic.Common
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Fintype.Sets

/-! Project-wide macros and notation, shared by many parts. Lowest file in the hierarchy. -/

/-- Discharges index-validity side goals of `l[i]` by `grind`. A definition whose unfolding
is needed is tagged `grind =` in a `_u` file (e.g. `Indices`, in `Basic_u`). -/
macro_rules
  | `(tactic| get_elem_tactic_extensible) => `(tactic| grind [List.getElem_mem])

/-- The tactic that fills `⟮p⟯` arguments. Extensible by `macro_rules`. -/
syntax "auto_prop" : tactic
macro_rules | `(tactic| auto_prop) => `(tactic| grind)

open Lean Elab Term in
/-- `(h : ⟮p⟯)`: an argument of type `p` whose proof is found automatically (by
`auto_prop`) when the caller omits it. Same as `(h : p := by auto_prop)`. -/
elab "⟮" p:term "⟯" : term => do
  let tac ← `(Lean.Parser.Tactic.tacticSeq| auto_prop)
  let name ← declareTacticSyntax tac
  elabType (← `(autoParam $p $(mkIdent name)))

/-- The maximum of a finite, nonempty set. -/
def maximum [LinearOrder α] (S : Set α) [Fintype S] (h : ⟮S.Nonempty⟯) : α :=
  S.toFinset.max' (Set.toFinset_nonempty.mpr h)

/-- List comprehension `[x ∈ l | p x]`: the elements of `l` satisfying `p`, in order, with
repeats; each comes with its proof of `x ∈ l` (available to `p`). -/
macro "[" x:ident " ∈ " l:term " | " p:term "]" : term =>
  `(List.filter (fun ⟨$x, _⟩ => decide $p) (List.attach $l))
