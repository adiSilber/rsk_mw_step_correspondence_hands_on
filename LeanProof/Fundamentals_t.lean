import Mathlib.Tactic.Common
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Synonym

/-! Project-wide macros and notation, shared by many parts. Lowest file in the hierarchy. -/

/-- Discharges index-validity side goals of `l[i]` by `grind`. A definition whose unfolding
is needed is tagged `grind =` in a `_u` file (e.g. `Indices`, in `Basic_u`). -/
macro_rules
  | `(tactic| get_elem_tactic_extensible) => `(tactic| grind [List.getElem_mem])

/-- `p → q` keeps the fact `p` available while reading `q`, so that `l[i]` inside `q` needs no
proof. The resulting proposition is unchanged. -/
macro_rules | `($p → $q) => `(∀ (_ : $p), $q)

/-- The tactic that finds omitted proof arguments (see the rule below): `decide` for concrete
examples (`_e` files), otherwise `grind`. The `_u` files teach it facts only through attributes
(`grind →`/`←`/`.`, `grind_pattern`, instances) — never by changing the tactic itself. -/
syntax "auto_prop" : tactic
macro_rules | `(tactic| auto_prop) => `(tactic| first | decide | grind)

/-- Whether the fundamental rule below is active. The `_u` files switch it off
(`set_option autoProp.rule false`): there every proof is written where Lean expects it. -/
register_option autoProp.rule : Bool := {
  defValue := true
  descr := "fill omitted proof arguments by `auto_prop` (switched off in `_u` files)" }

namespace AutoProp
open Lean Elab Term Meta

/-- If `e` still expects a proof argument, the proposition it expects. (Only abbreviations are
looked through: `a ≠ b` or `¬ p` is a statement, not a term waiting for a proof of `a = b`.) -/
def missingProof? (e : Expr) : TermElabM (Option Expr) := do
  let .forallE _ p _ _ ← whnfR (← instantiateMVars (← inferType e)) | return none
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
    -- (a placeholder standing for a proof, e.g. an index bound, does not count)
    let untyped ← (← getLCtx).getFVarIds.filterM fun f => do
      (← getMVars (← instantiateMVars (← f.getType))).anyM fun mv => do
        pure !(← isProp (← mv.getType))
    let goal ← h.mvarId!.tryClearMany untyped
    let [] ← Tactic.run goal (Tactic.evalTactic (← `(tactic| auto_prop)))
      | throwError "unsolved"
    -- the search may not decide placeholders that belong to the surrounding term
    for (mv, _) in (← getMCtx).eAssignment.toList do
      if mctx₀.decls.contains mv && !mctx₀.eAssignment.contains mv then
        throwError "the proof search touched the surrounding term"
    pure h

/-- The type of a term once the proof arguments it still expects are supplied (as long as the
type does not depend on them). -/
partial def resultType (ty : Expr) : TermElabM Expr := do
  let ty ← instantiateMVars ty
  if let .forallE _ p b _ ← whnfR ty then
    if (← isProp p) && !b.hasLooseBVars then return ← resultType b
  return ty

/-- The proofs `e` still expects, found by `auto_prop`. A proof may be left for later when the
term is clearly not meant as a function: a type is expected, or the term is an object (not a
proof) that is not a function once its proofs are supplied. -/
def fillProofs (e : Expr) (expected? : Option Expr) : TermElabM Expr := do
  let later ← match expected? with
    | some _ => pure true
    | none => do
      let ty ← inferType e
      let r ← whnf (← resultType ty)
      pure (!(← isProp ty) && !r.isForall && !r.isMVar)
  let mut e := e
  repeat
    let some p ← missingProof? e | break
    let some h ← prove? p later | break
    e := mkApp e h
  return e

/-- Fundamental rule: when an application `f a b` still expects proof arguments (and no
function is expected), each missing proof is found by `auto_prop`. -/
@[term_elab app] def elabApp' : TermElab := fun stx expected? => do
  unless (← getOptions).getBool `autoProp.rule true do throwUnsupportedSyntax
  -- an expected type that is still a placeholder counts as unknown
  let expected? ← match expected? with
    | some t => do let t ← instantiateMVars t; pure (if t.isMVar then none else some t)
    | none => pure none
  let e ← elabApp stx expected?
  if let some t := expected? then
    if (← whnf t).isForall then return e        -- a function is wanted: leave it alone
    -- the type once the proofs are supplied is the expected one: say so now, so that the
    -- parts of the term still waiting for their type can proceed before the proofs are sought
    discard <| observing? (isDefEq (← resultType (← inferType e)) t)
  fillProofs e expected?

/-- The same rule for the head of a field access, `(f a b).field` or `(x.f).field`: the head
is read first and, when it is an object, its missing proofs are filled; then the field is
taken. (An application is already complete after reading; a proof is left alone.) -/
@[term_elab proj] def elabProj' : TermElab := fun stx expected? => do
  unless (← getOptions).getBool `autoProp.rule true do throwUnsupportedSyntax
  let head := stx[0]
  let inner := if head.isOfKind ``Parser.Term.paren then head[1] else head
  unless inner.isOfKind ``Parser.Term.app || inner.isOfKind ``Parser.Term.proj
      || inner.isIdent do throwUnsupportedSyntax
  let e ← elabTerm inner none
  let e' ← if inner.isOfKind ``Parser.Term.app || (← isProp (← inferType e)) then pure e
    else fillProofs e none
  -- a head that needed nothing is read as usual
  if !inner.isOfKind ``Parser.Term.app && e' == e then throwUnsupportedSyntax
  elabTerm (stx.setArg 0 (← exprToSyntax e')) expected?

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

-- Facts `auto_prop` needs for the proofs omitted below and in `Basic_t`: membership in
-- `l.toFinset` and in `l.map f`, what an injective function is, and that `toLex` is one.
attribute [grind =] List.mem_toFinset List.mem_map toLex_inj
attribute [grind] Function.Injective

/-- The members of a list form a finite set (computed by `l.toFinset`); so do their images. -/
instance {α} [DecidableEq α] (l : List α) : Fintype {x | x ∈ l} := Fintype.ofFinset l.toFinset
instance {α β} [DecidableEq β] (l : List α) (f : α → β) : Fintype {y | ∃ x ∈ l, f x = y} :=
  Fintype.ofFinset (l.map f).toFinset

/-- The members of `a :: l`, and their images, form nonempty sets (witness `a`, `f a`). -/
instance {α} (a : α) (l : List α) : Nonempty ↥{x | x ∈ a :: l} :=
  Set.Nonempty.to_subtype (Set.nonempty_of_mem (s := {x | x ∈ a :: l}) (x := a))
instance {α β} (s : α) (ss : List α) (f : α → β) : Nonempty ↥{y | ∃ x ∈ s :: ss, f x = y} :=
  Set.Nonempty.to_subtype (Set.nonempty_of_mem (s := {y | ∃ x ∈ s :: ss, f x = y}) (x := f s))

/-- The maximum of a finite, nonempty set. -/
def maximum [LinearOrder α] (S : Set α) [Fintype S] (h : S.Nonempty) : α :=
  S.toFinset.max' (Set.toFinset_nonempty.mpr h)

/-- The first element of a finite, nonempty set. -/
def first [LinearOrder α] (S : Set α) [Fintype S] (h : S.Nonempty) : α :=
  S.toFinset.min' (Set.toFinset_nonempty.mpr h)

/-- The elements of a finite set, in increasing order. -/
def sorted [LinearOrder α] (S : Set α) [Fintype S] : List α :=
  S.toFinset.sort (· ≤ ·)

/-- The elements of a list in increasing order, repeats kept. -/
def List.increasing [LinearOrder α] (l : List α) : List α := l.insertionSort (· ≤ ·)
-- `auto_prop` knows what it is, and (Mathlib) that an insertion sort is sorted.
attribute [grind] List.increasing
attribute [grind .] List.pairwise_insertionSort

/-- `let x ∈ S; e`: `e` for an arbitrary element `x` of `S`. It is well defined because `e`
takes the same value at every element of `S` — a proof Lean demands (and `auto_prop` finds),
together with `S` being nonempty. (To compute, `e` is evaluated at `first S`.) -/
def anyOf [LinearOrder α] (S : Set α) [Fintype S] (f : (x : α) → x ∈ S → β) (h : S.Nonempty)
    (_hf : ∀ x (hx : x ∈ S) y (hy : y ∈ S), f x hx = f y hy) : β :=
  f (first S h) (Set.mem_toFinset.mp (Finset.min'_mem _ _))

syntax "let " ident " ∈ " term "; " term : term

open Lean Elab Term Meta in
elab_rules : term <= expected
  | `(let $x:ident ∈ $S; $e) => do
    -- `e` is read completely first (as a function of `x`), so that the two facts behind
    -- `anyOf` are asked about a finished term
    let S ← elabTerm S none
    let expected ← instantiateMVars expected
    let body ← if expected.isMVar then pure e else `(($e : $(← exprToSyntax expected)))
    let f ← elabTerm (← `(fun $x (_ : $x ∈ $(← exprToSyntax S)) => $body)) none
    synthesizeSyntheticMVarsNoPostponing
    elabTerm (← `(anyOf $(← exprToSyntax S) $(← exprToSyntax f))) (some expected)

/-- List comprehension `[x ∈ l | p x]`: the elements of `l` satisfying `p`, in order, with
repeats; each comes with its proof of `x ∈ l` (available to `p`). -/
macro "[" x:ident " ∈ " l:term " | " p:term "]" : term =>
  `(List.filter (fun ⟨$x, _⟩ => decide $p) (List.attach $l))

/-- List comprehension `[f | b₁, …, bₙ]`: the values of `f` for each choice of the binders,
in order, with repeats. A binder is `x ∈ l`, `k ≤ n`, `k < n`, or a condition `p` (keeping
only the choices for which it holds; it comes last). Inside `f` (and in later binders) the facts
`x ∈ l`, `k ≤ n`, `k < n` and `p` are available, so that `l'[x]`-like terms need no proof. -/
declare_syntax_cat comprehension_binder
syntax (name := memBinder) ident " ∈ " term : comprehension_binder
syntax (name := leBinder) ident " ≤ " term : comprehension_binder
syntax (name := ltBinder) ident " < " term : comprehension_binder
syntax (name := condBinder) (priority := low) term : comprehension_binder
syntax (name := comprehension) "[" term " | " comprehension_binder,+ "]" : term

-- Binder by binder, from the left: `x ∈ l` ranges over `l.attach` (each `x` comes with its
-- proof of `x ∈ l`), `k ≤ n` and `k < n` range over `List.range`, and a condition `p` is an
-- `if` that keeps its proof at hand. The last binder maps, the earlier ones flat-map.
-- (One rule per command: a single `macro_rules` with all of them is too slow to compile.
-- A later rule is tried first, so the one-binder rules come last.)
macro_rules
  | `([$f | $x:ident ∈ $l, $bs,*]) =>
    `(List.flatMap (fun ⟨$x, hx⟩ => [$f | $bs,*]) (List.attach $l))
macro_rules | `([$f | $k:ident ≤ $n, $bs,*]) => `([$f | $k:ident ∈ List.range ($n + 1), $bs,*])
macro_rules | `([$f | $k:ident < $n, $bs,*]) => `([$f | $k:ident ∈ List.range $n, $bs,*])
macro_rules | `([$f | $x:ident ∈ $l]) => `(List.map (fun ⟨$x, hx⟩ => $f) (List.attach $l))
macro_rules | `([$f | $k:ident ≤ $n]) => `([$f | $k:ident ∈ List.range ($n + 1)])
macro_rules | `([$f | $k:ident < $n]) => `([$f | $k:ident ∈ List.range $n])
macro_rules | `([$f | $p:term]) => `(if h : $p then [$f] else [])
