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
  if let .forallE _ p b _ ← whnf ty then
    if (← isProp p) && !b.hasLooseBVars then return ← resultType b
  return ty

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
    -- the type once the proofs are supplied is the expected one: say so now, so that the
    -- parts of the term still waiting for their type can proceed before the proofs are sought
    discard <| observing? (isDefEq (← resultType (← inferType e)) t)
  -- a proof may be left for later when the term is clearly not meant as a function: a type
  -- is expected, or the term is an object (not a proof) that is not a function once its
  -- proofs are supplied
  let later ← match expected? with
    | some _ => pure true
    | none => do
      let ty ← inferType e
      let r ← whnf (← resultType ty)
      pure (!(← isProp ty) && !r.isForall && !r.isMVar)
  -- inside a comprehension body, a proof is not left for later: a fact that is not at hand
  -- becomes a condition of the comprehension instead
  let later := later && !(← getOptions).getBool `autoProp.noDefer
  repeat
    let some p ← missingProof? e | break
    let some h ← prove? p later | break
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
in order, with repeats. A binder is `x ∈ l`, `(x, y) ∈ l`, `k ≤ n`, `k < n`, or a condition
`p` (keeping only the choices for which it holds); a name already bound (by an earlier binder,
or outside, like `s.a`) makes `x ∈ l`, `k ≤ n`, `k < n` conditions too. Inside `f` (and in
later binders) the facts `x ∈ l` and `p` are available, so that `l'[x]`-like terms need no
proof; and when `f` needs a fact that does not follow from them, that fact becomes one more
condition: the choices for which `f` is not defined are skipped. -/
declare_syntax_cat comprehension_binder
syntax (name := memBinder) ident " ∈ " term : comprehension_binder
syntax (name := pairBinder) "(" ident ", " ident ")" " ∈ " term : comprehension_binder
syntax (name := leBinder) ident " ≤ " term : comprehension_binder
syntax (name := ltBinder) ident " < " term : comprehension_binder
syntax (name := condBinder) (priority := low) term : comprehension_binder
syntax (name := comprehension) "[" term " | " comprehension_binder,+ "]" : term

namespace Comprehension
open Lean Elab Term Meta

/-- `[e]`, and `[]` of the type of `e`. -/
private def singleton (e : Expr) : MetaM Expr := do
  mkAppM ``List.cons #[e, ← mkAppOptM ``List.nil #[some (← inferType e)]]

/-- `if h : p then t h else []`, for `t : p → List β`. -/
private def guard (p t : Expr) : MetaM Expr := do
  let β ← withLocalDecl `h .default p fun h => inferType (t.beta #[h])
  let nil ← mkAppOptM ``List.nil #[some (← whnf β).appArg!]
  let e ← withLocalDecl `h .default (mkNot p) fun h => mkLambdaFVars #[h] nil
  mkAppOptM ``dite #[some β, some p, none, some t, some e]

/-- The body `f`, read with the facts of the binders at hand: one value, or — when it needs a
fact that is not at hand — the list of it under that fact as a condition. -/
private def body (f : Term) (expected? : Option Expr) : TermElabM (Expr × Bool) := do
  let e ← withTheReader Core.Context
    (fun c => { c with options := c.options.setBool `autoProp.noDefer true }) do
    let settled (e? : Option Expr) : TermElabM Expr := do
      let e ← elabTerm f e?
      synthesizeSyntheticMVarsNoPostponing
      pure e
    match ← observing? (settled none) with
    | some e => pure e
    | none => settled expected?
  let e ← instantiateMVars e
  let ty ← whnf (← inferType e)
  if let .forallE _ p β _ := ty then
    if (← isProp p) && !β.hasLooseBVars then
      let t ← withLocalDecl `h .default p fun h => do
        let one ← singleton (mkApp e h)
        mkLambdaFVars #[h] one
      return (← guard p t, true)
  return (e, false)

/-- The binders, left to right; returns the list, and whether it is a list (always, here) or
a single value (the body alone). -/
private partial def go (f : Term) (bs : Array Syntax) (i : Nat) (bound : Array Name)
    (expected? : Option Expr) : TermElabM (Expr × Bool) := do
  if h : i < bs.size then
    let b := bs[i]
    let fresh (x : Syntax) : Bool := x.getId.isAtomic && !bound.contains x.getId
    if b.isOfKind ``memBinder && fresh b[0] then
      ranging #[b[0].getId] (← elabTerm b[2] none)
    else if b.isOfKind ``pairBinder then
      ranging #[b[1].getId, b[3].getId] (← elabTerm b[6] none)
    else if b.isOfKind ``leBinder && fresh b[0] then
      ranging #[b[0].getId] (← elabTerm (← `(List.range ($(⟨b[2]⟩) + 1))) none)
    else if b.isOfKind ``ltBinder && fresh b[0] then
      ranging #[b[0].getId] (← elabTerm (← `(List.range $(⟨b[2]⟩))) none)
    else
      let p : Term ←
        if b.isOfKind ``memBinder then `($(⟨b[0]⟩):term ∈ $(⟨b[2]⟩))
        else if b.isOfKind ``leBinder then `($(⟨b[0]⟩):term ≤ $(⟨b[2]⟩))
        else if b.isOfKind ``ltBinder then `($(⟨b[0]⟩):term < $(⟨b[2]⟩))
        else pure ⟨b[0]⟩
      let p ← elabTerm p (some (mkSort levelZero))
      synthesizeSyntheticMVarsNoPostponing
      let p ← instantiateMVars p
      let t ← withLocalDecl `h .default p fun h => do
        let (inner, isList) ← go f bs (i + 1) bound expected?
        let inner ← if isList then pure inner else singleton inner
        mkLambdaFVars #[h] inner
      return (← guard p t, true)
  else
    body f expected?
where
  /-- `x` (or `(x, y)`) ranges over the list `l`: the rest, over `l.attach`. -/
  ranging (names : Array Name) (l : Expr) : TermElabM (Expr × Bool) := do
    synthesizeSyntheticMVarsNoPostponing
    let l ← instantiateMVars l
    let lty ← whnf (← instantiateMVars (← inferType l))
    unless lty.isAppOfArity ``List 1 do throwError "a comprehension ranges over a list, not {lty}"
    let α := lty.appArg!
    let memPred ← withLocalDecl `a .default α fun a => do
      mkLambdaFVars #[a] (← mkAppM ``Membership.mem #[l, a])
    let subty ← mkAppM ``Subtype #[memPred]
    let attached ← mkAppM ``List.attach #[l]
    withLocalDecl `s .default subty fun s => do
      let sval := mkProj ``Subtype 0 s
      let sprop := mkProj ``Subtype 1 s
      let (lam, isList) ←
        if names.size == 1 then
          withLocalDecl names[0]! .default α fun x => do
            withLocalDecl `h .default (← mkAppM ``Membership.mem #[l, x]) fun hx => do
              let (inner, isList) ← go f bs (i + 1) (bound ++ names) expected?
              let fn ← mkLambdaFVars #[x, hx] inner
              pure (← mkLambdaFVars #[s] (fn.beta #[sval, sprop]), isList)
        else do
          let pty ← whnf α
          unless pty.isAppOfArity ``Prod 2 do throwError "`(x, y) ∈ l` needs a list of pairs"
          withLocalDecl names[0]! .default pty.appFn!.appArg! fun x => do
          withLocalDecl names[1]! .default pty.appArg! fun y => do
            let pair ← mkAppM ``Prod.mk #[x, y]
            withLocalDecl `h .default (← mkAppM ``Membership.mem #[l, pair]) fun hxy => do
              let (inner, isList) ← go f bs (i + 1) (bound ++ names) expected?
              let fn ← mkLambdaFVars #[x, y, hxy] inner
              let fst := mkProj ``Prod 0 sval
              let snd := mkProj ``Prod 1 sval
              pure (← mkLambdaFVars #[s] (fn.beta #[fst, snd, sprop]), isList)
      let e ← mkAppM (if isList then ``List.flatMap else ``List.map) #[lam, attached]
      return (e, true)

@[term_elab comprehension] def elab' : TermElab := fun stx expected? => do
  let elemExpected? ← match expected? with
    | some t => do
      let t ← whnf (← instantiateMVars t)
      pure (if t.isAppOfArity ``List 1 then some t.appArg! else none)
    | none => pure none
  let (e, _) ← go ⟨stx[1]⟩ stx[3].getSepArgs 0 #[] elemExpected?
  return e

end Comprehension


-- todo: write the autogenerate versions of maximum for other set functions
