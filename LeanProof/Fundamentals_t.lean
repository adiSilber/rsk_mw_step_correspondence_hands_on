import Mathlib.Tactic.Common
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Finset.Sort

/-! Project-wide macros and notation, shared by many parts. Lowest file in the hierarchy. -/

/-- Discharges index-validity side goals of `l[i]` by `grind`. A definition whose unfolding
is needed is tagged `grind =` in a `_u` file (e.g. `Indices`, in `Basic_u`). -/
macro_rules
  | `(tactic| get_elem_tactic_extensible) => `(tactic| grind [List.getElem_mem])

/-- `p → q` keeps the fact `p` available while reading `q`, so that `l[i]` inside `q` needs no
proof. The resulting proposition is unchanged. -/
macro_rules | `($p → $q) => `(∀ (_ : $p), $q)

/-- The tactic that finds omitted proof arguments (see the rule below). `grind`, extended by
`macro_rules` in `_u` files with the facts it should know. -/
syntax "auto_prop" : tactic
macro_rules | `(tactic| auto_prop) => `(tactic| grind)

namespace AutoProp
open Lean Elab Term Meta

/-- If `e` still expects a proof argument, the proposition it expects. -/
def missingProof? (e : Expr) : TermElabM (Option Expr) := do
  let .forallE _ p _ _ ← whnf (← instantiateMVars (← inferType e)) | return none
  return if ← isProp p then some p else none

/-- A proof of `p` by `auto_prop`, found right now if possible; if `later`, it may also be
left for the end of elaboration (when more is known), otherwise the result is `none`. -/
def prove? (p : Expr) (later : Bool) : TermElabM (Option Expr) := do
  if let some h ← proveNow? p then return some h
  if later then return some (← elabTermEnsuringType (← `(by auto_prop)) p)
  return none
where
  /-- `observing?` undoes any partial progress if the proof is not found. -/
  proveNow? (p : Expr) : TermElabM (Option Expr) := observing? do
    let mctx₀ ← getMCtx
    let h ← mkFreshExprMVar p
    -- hypotheses whose type is still a placeholder are not facts: hide them from the search
    let untyped ← (← getLCtx).getFVarIds.filterM fun f => do
      pure (← instantiateMVars (← f.getType)).hasExprMVar
    let goal ← h.mvarId!.tryClearMany untyped
    let [] ← Tactic.run goal (Tactic.evalTactic (← `(tactic| auto_prop)))
      | throwError "unsolved"
    -- the search may not decide placeholders that belong to the surrounding term
    for (mv, _) in (← getMCtx).eAssignment.toList do
      if mctx₀.decls.contains mv && !mctx₀.eAssignment.contains mv then
        throwError "the proof search touched the surrounding term"
    pure h

/-- Fundamental rule: when an application `f a b` still expects proof arguments (and no
function is expected), each missing proof is found by `auto_prop`. -/
@[term_elab app] def elabApp' : TermElab := fun stx expected? => do
  -- an expected type that is still a placeholder counts as unknown
  let expected? ← match expected? with
    | some t => do let t ← instantiateMVars t; pure (if t.isMVar then none else some t)
    | none => pure none
  let mut e ← elabApp stx expected?
  if let some t := expected? then
    if (← whnf t).isForall then return e        -- a function is wanted: leave it alone
  repeat
    let some p ← missingProof? e | break
    let some h ← prove? p (later := expected?.isSome) | break
    e := mkApp e h
  return e

/-- The same rule for the head of a field access, `(f a b).field`: the head is read first (so
its missing proofs are filled), then the field is taken. -/
@[term_elab proj] def elabProj' : TermElab := fun stx expected? => do
  let head := stx[0]
  let inner := if head.isOfKind ``Parser.Term.paren then head[1] else head
  unless inner.isOfKind ``Parser.Term.app do throwUnsupportedSyntax
  let e ← elabTerm inner none
  let stx' := stx.setArg 0 (← exprToSyntax e)
  elabTerm stx' expected?

end AutoProp

/-- `x ∈ s` reads the container `s` first, so that `x` is converted to its element type
(e.g. an index `n : Fin k` may be tested for membership in a `List ℕ`). -/
syntax "mem_coe% " term:max ppSpace term:max : term

open Lean Elab Term Meta in
elab_rules : term <= expected?
  | `(mem_coe% $s $x) => do
    let s ← elabTerm s none
    let γ ← instantiateMVars (← inferType s)
    let u ← mkFreshLevelMVar; let v ← mkFreshLevelMVar
    let α ← mkFreshTypeMVar
    if !γ.hasExprMVar then
      -- the container's type is known: fix the element type first, then read `x` against it
      if let some inst ← observing? (synthInstance (mkApp2 (.const ``Membership [u, v]) α γ)) then
        let x ← elabTermEnsuringType x (← instantiateMVars α)
        return mkApp5 (.const ``Membership.mem [u, v]) α γ inst s x
    -- otherwise: the ordinary reading of `Membership.mem s x`
    elabAppArgs (.const ``Membership.mem [u, v]) #[] #[.expr s, .stx x] expected?
      (explicit := false) (ellipsis := false)

macro_rules | `($x ∈ $s) => `(mem_coe% $s $x)

/-- A list can be used where a set is expected: the set of its members. -/
instance {α} : Coe (List α) (Set α) := ⟨fun l => {x | x ∈ l}⟩

/-- The maximum of a finite, nonempty set. -/
def maximum [LinearOrder α] (S : Set α) [Fintype S] (h : S.Nonempty) : α :=
  S.toFinset.max' (Set.toFinset_nonempty.mpr h)

/-- The first element of a finite, nonempty set. -/
def first [LinearOrder α] (S : Set α) [Fintype S] (h : S.Nonempty) : α :=
  S.toFinset.min' (Set.toFinset_nonempty.mpr h)

/-- The elements of a finite set, in increasing order. -/
def sorted [LinearOrder α] (S : Set α) [Fintype S] : List α :=
  S.toFinset.sort (· ≤ ·)

/-- List comprehension `[x ∈ l | p x]`: the elements of `l` satisfying `p`, in order, with
repeats; each comes with its proof of `x ∈ l` (available to `p`). -/
macro "[" x:ident " ∈ " l:term " | " p:term "]" : term =>
  `(List.filter (fun ⟨$x, _⟩ => decide $p) (List.attach $l))

/-- List comprehension `[f x | x ∈ l]`: `f x` for each `x` of `l`, in order, with repeats;
the proof of `x ∈ l` is available to `f`. -/
macro "[" f:term " | " x:ident " ∈ " l:term "]" : term =>
  `(List.map (fun ⟨$x, _⟩ => $f) (List.attach $l))

/-- The same over a list of pairs: `[f x y | (x, y) ∈ l]`. -/
macro "[" f:term " | " "(" x:ident ", " y:ident ")" " ∈ " l:term "]" : term =>
  `(List.map (fun ⟨⟨$x, $y⟩, _⟩ => $f) (List.attach $l))

/-- The consecutive pairs `(l₀, l₁), (l₁, l₂), …` of a list. -/
abbrev consecutive {α} (l : List α) : List (α × α) := l.zip l.tail

-- todo: write the autogenerate versions of maximum for other set functions
