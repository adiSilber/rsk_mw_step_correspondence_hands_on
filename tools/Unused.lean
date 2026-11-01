import Lean
import LeanProof
open Lean

/-!
# Unused declarations (ESSENTIALS rule 12)

Run after `lake build`:

    lake env lean tools/Unused.lean

Loads the built project and prints two lists:

* **A.** declarations no other declaration mentions (in a statement or a proof);
* **B.** declarations that are mentioned, but on which `corollary_3_4` does not depend.

"Mentions" is read off the elaborated terms, so uses by `grind`, `simp` and omitted proofs
count. Two kinds of use leave no trace and must be checked by hand: coercion instances (a
coercion is unfolded where it is written) and `rfl` lemmas (`simp` rewrites with them without
recording them). The `_e` files are not imported here when they are commented out; a
declaration used only by an eval therefore appears in list A.

Compiler auxiliaries (`_proof_n`, `match_n`, `eq_n`, `congr_simp`, …) are folded into the
declaration they belong to. A shared `_proof_n` (Lean reuses identical proofs across
declarations of one file) is not counted as a mention of its owner.
-/

/-- Name components that mark a compiler or elaborator auxiliary under an owner declaration. -/
def auxComp (s : String) : Bool :=
  s.startsWith "_" || s.startsWith "eq_" || s.startsWith "match_" || s.startsWith "proof_" ||
  s.isNat || s == "induct" || s == "rec" || s == "recOn" || s == "casesOn" || s == "mk" ||
  s == "noConfusion" || s == "noConfusionType" || s == "injEq" || s == "inj" ||
  s == "sizeOf_spec" || s == "below" || s == "brecOn" || s == "binductionOn" ||
  s == "ibelow" || s == "ctorIdx" || s == "ctorElim" || s == "spec" || s == "go" ||
  s == "congr_simp" || s == "splitter"

/-- The user-facing declaration an auxiliary constant belongs to. -/
partial def owner : Name → Name
  | n@(.str p s) => if auxComp s then owner p else n
  | n => n

/-- Like `owner`, but `none` when the path goes through a (possibly shared) `_proof_n`. -/
partial def ownerNP : Name → Option Name
  | n@(.str p s) => if s.startsWith "_proof" || s.startsWith "proof_" then none
                    else if auxComp s then ownerNP p else some n
  | n => some n

def isProj (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => (env.header.moduleNames[i.toNat]!).getRoot == `LeanProof
  | none => false

def modOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => ((env.header.moduleNames[i.toNat]!).toString.drop 10).toString
  | none => ""

def kindOf (env : Environment) (n : Name) (ci : ConstantInfo) : String :=
  if Lean.Meta.isInstanceCore env n then "instance"
  else match ci with
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor" | .axiomInfo _ => "axiom" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | .recInfo _ => "rec"

def show' (n : Name) : String :=
  match privateToUserName? n with
  | some u => s!"{u} (private)"
  | none => s!"{n}"

def refsOf (ci : ConstantInfo) : Array Name :=
  ci.type.getUsedConstants ++ (match ci.value? with | some v => v.getUsedConstants | none => #[])

#eval show CoreM Unit from do
  let env ← getEnv
  let proj := env.constants.map₁.toList.filter (fun (n, _) => isProj env n)
  -- A: mentioned by a constant outside itself (not through shared proofs)
  let mut used : NameSet := {}
  for (u, ci) in proj do
    let U := owner u
    for c in refsOf ci do
      if let some C := ownerNP c then
        if C != U then used := used.insert C
  -- B: reachable from corollary_3_4
  let mut reached : NameSet := {}
  let mut queue : Array Name := #[`corollary_3_4]
  while h : queue.size > 0 do
    let n := queue.back
    queue := queue.pop
    if reached.contains n then continue
    reached := reached.insert n
    if let some ci := env.find? n then
      if isProj env n then
        for c in refsOf ci do
          if !reached.contains c then queue := queue.push c
  let mut rowsA : Array String := #[]
  let mut rowsB : Array String := #[]
  for (n, ci) in proj do
    if owner n != n then continue
    let k := kindOf env n ci
    if k == "rec" || k == "ctor" || k == "quot" then continue
    -- syntax, macro and elaborator machinery
    if ci.type.getUsedConstants.any (fun c => c.getRoot == `Lean) then continue
    let row := s!"{modOf env n}: {k}  {show' n}"
    if !used.contains n then rowsA := rowsA.push row
    else if !reached.contains n then rowsB := rowsB.push row
  IO.println "== A. mentioned by nothing in the built project =="
  for r in rowsA.qsort (· < ·) do IO.println r
  IO.println "== B. mentioned, but not needed for corollary_3_4 =="
  for r in rowsB.qsort (· < ·) do IO.println r
  IO.println s!"-- {proj.length} project constants"
