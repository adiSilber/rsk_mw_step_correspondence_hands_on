import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.MW1_t
import Mathlib.Data.List.Permutation
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Chain

set_option linter.style.setOption false
set_option autoProp.rule false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.style.show false
set_option linter.hashCommand false

open scoped List

/-!
# Mœglin–Waldspurger, part 1: proofs

Decidability, chain-preservation of the greedy scan, its proof-carrying
packagings (`extendChain`, `Proof.greedyChain`, `mwStep`), and the greedy-optimality
API consumed by `chainLenPreserved` (Prop 3.3).
-/

/-- `isChain` is Mathlib's `IsChain chainLink` (consecutive elements linked): the form the
proofs work with. -/
lemma isChain_iff {l : List Segment} : isChain l ↔ l.IsChain chainLink :=
  (List.isChain_iff_getElem (R := chainLink)).symm

instance (l : List Segment) : Decidable (isChain l) := decidable_of_iff _ isChain_iff.symm

/-- The greedy scan: appends `s` to the chain whenever it forms a `chainLink` with the
current last. It produces a sequence of leading indices (`greedyIdx_mem_leadingIndices`), and
every sequence of leading indices gives the same segments (`segsAt_eq_greedy`). -/
private def extendChain.go (m : List Segment) (chain : List Segment) (hne : chain ≠ []) :
    List Segment :=
  match m with
  | []      => chain
  | s :: rest =>
    if h : chainLink (chain.getLast hne) s then
      extendChain.go rest (chain ++ [s]) (by simp)
    else
      extendChain.go rest chain hne

namespace Proof

/-- `⁻Δ` as a computation: `[a, b] → [a+1, b]`, and nothing for a singleton. -/
def shorten (s : Segment) : Option Segment :=
  if h : s.a < s.b then some (segmentResidual s h) else none

/-- Remove the chain's segments from `m`, add back their residuals `⁻Δ`, then re-sort: the
computation behind `makeResidual` (`residual_eq`). -/
def residualAlong (m : Multisegment) (chain : List Segment) : Multisegment :=
  let m_without := chain.foldl List.erase m.segments
  let residuals := chain.filterMap Proof.shorten
  ⟨(m_without ++ residuals).insertionSort (· ≤ ·), List.pairwise_insertionSort _ _⟩

end Proof

/-- A `chainLink` between two segments implies strict lex order. -/
lemma chainLink_imp_lt (s₁ s₂ : Segment) (h : chainLink s₁ s₂) : s₁ < s₂ :=
  (Segment.lt_def _ _).mpr (Or.inl h.1.1)

/-- An `isChain` list is also lex-sorted under `≤`. -/
lemma isChain_imp_sorted (l : List Segment) (h : isChain l) : l.Pairwise (· ≤ ·) := by
  have h_lt : l.IsChain (· < ·) := (isChain_iff.mp h).imp chainLink_imp_lt
  exact h_lt.pairwise.imp le_of_lt

/-- Snoc preserves `isChain` when the new last element has a `chainLink` from the
    previous last. -/
lemma isChain_snoc (l : List Segment) (hne : l ≠ [])
    (h : isChain l) (x : Segment) (h_link : chainLink (l.getLast hne) x) :
    isChain (l ++ [x]) := by
  refine isChain_iff.mpr (List.IsChain.append (isChain_iff.mp h) (List.IsChain.singleton x) ?_)
  intro a ha b hb
  rw [List.getLast?_eq_some_getLast hne, Option.mem_def, Option.some.injEq] at ha
  rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
  rw [← ha, ← hb]
  exact h_link

/-- `extendChain.go` preserves `isChain`. -/
lemma extendChain.go_isChain
    (m : List Segment) (chain : List Segment) (hne : chain ≠ [])
    (h_chain : isChain chain) : isChain (extendChain.go m chain hne) := by
  induction m generalizing chain hne h_chain with
  | nil => exact h_chain
  | cons s rest ih =>
    rw [extendChain.go]
    split_ifs with hcl
    · exact ih _ _ (isChain_snoc chain hne h_chain s hcl)
    · exact ih _ _ h_chain

/-- Extend `c` by scanning the sorted multisegment `m` for the next chain link:
the proof-carrying packaging of `extendChain.go`. -/
private def extendChain (m : Multisegment) (c : Chain) (hne : c.val.segments ≠ []) : Chain :=
  let result : List Segment := extendChain.go m.segments c.val.segments hne
  have h_chain : isChain result :=
    extendChain.go_isChain m.segments c.val.segments hne c.property
  have h_sorted : result.Pairwise (· ≤ ·) := isChain_imp_sorted _ h_chain
  let result_ms : Multisegment := { segments := result, is_sorted := h_sorted }
  ⟨result_ms, h_chain⟩

namespace Proof

/-- The leading chain of `m`: starts from the minimum segment and greedily
    extends as far as possible through the sorted list. -/
def greedyChain (m : Multisegment) : Chain :=
  match h : m.segments with
  | []            => ⟨⟨[], by simp⟩, by simp [isChain]⟩
  | first :: rest =>
    extendChain
      ⟨rest, (List.pairwise_cons.mp (h ▸ m.is_sorted)).2⟩
      -- the singleton chain `[first]` is vacuously a chain
      ⟨⟨[first], by simp⟩, by simp [isChain]⟩
      (by simp)

end Proof

/-! ## Downstream API

These lemmas are not used elsewhere in this file. They record facts that are true of the
definitions above (`isChain`, `extendChain`, `Proof.greedyChain`) for the benefit of consumers
in other files — currently `chainLenPreserved` in `Corollary34`. -/

/-- In a chain, the `i`-th segment's begin is the head's begin plus `i`. -/
lemma chain_get_a : ∀ (l : List Segment), isChain l →
    ∀ (i : ℕ) (s t : Segment), l[0]? = some s → l[i]? = some t → t.a = s.a + (i : ℤ) := by
  intro l
  induction l with
  | nil => intro _ i s t h0 _; simp at h0
  | cons x xs ih =>
    intro h i s t h0 hi
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0; subst h0
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi; simp
    | succ j =>
      rw [List.getElem?_cons_succ] at hi
      rw [isChain_iff, List.isChain_cons] at h
      obtain ⟨hlink, htail⟩ := h
      cases xs with
      | nil => simp at hi
      | cons y ys =>
        have hya : y.a = x.a + 1 := (hlink y (by simp)).2
        have hrec := ih (isChain_iff.mpr htail) j y t (by simp) hi
        rw [hrec, hya]; omega

/-- Every element of `extendChain.go ms chain hne` is in `chain` or in `ms`. -/
lemma extendChain.go_mem (ms chain : List Segment) (hne : chain ≠ []) :
    ∀ x ∈ extendChain.go ms chain hne, x ∈ chain ∨ x ∈ ms := by
  induction ms generalizing chain hne with
  | nil => intro x hx; left; rwa [extendChain.go] at hx
  | cons s rest ih =>
    intro x hx
    rw [extendChain.go] at hx
    split_ifs at hx with h
    · rcases ih (chain ++ [s]) (by simp) x hx with hc | hr
      · rcases List.mem_append.mp hc with h1 | h1
        · exact Or.inl h1
        · simp at h1; subst h1; exact Or.inr (by simp)
      · exact Or.inr (by simp [hr])
    · rcases ih chain hne x hx with hc | hr
      · exact Or.inl hc
      · exact Or.inr (by simp [hr])

/-- The leading chain's segments are all members of `m`. -/
lemma greedyChain_subset (m : Multisegment) (x : Segment)
    (hx : x ∈ (Proof.greedyChain m).val.segments) : x ∈ m.segments := by
  unfold Proof.greedyChain at hx
  split at hx
  · simp at hx
  · rename_i first rest heq
    rcases extendChain.go_mem _ _ _ x hx with hc | hr
    · simp only [List.mem_singleton] at hc; subst hc; rw [heq]; exact List.mem_cons_self
    · rw [heq]; exact List.mem_cons_of_mem _ hr

/-- `extendChain.go` preserves the chain's head (it only appends). -/
lemma extendChain.go_head (ms chain : List Segment) (hne : chain ≠ []) :
    (extendChain.go ms chain hne).head? = chain.head? := by
  induction ms generalizing chain hne with
  | nil => rw [extendChain.go]
  | cons s rest ih =>
    rw [extendChain.go]; split_ifs with h
    · rw [ih]; cases chain with | nil => simp at hne | cons a t => simp
    · rw [ih]

/-- The leading chain starts at the minimum segment `min m`. -/
lemma greedyChain_head (m : Multisegment) (sₘ : Segment) (h : m.segments.head? = some sₘ) :
    (Proof.greedyChain m).val.segments.head? = some sₘ := by
  unfold Proof.greedyChain
  split
  · rename_i heq; rw [heq] at h; simp at h
  · rename_i first rest heq
    rw [heq] at h; simp only [List.head?_cons, Option.some.injEq] at h
    simp only [extendChain, extendChain.go_head, List.head?_cons]; rw [h]

/-- The leading chain is a `≪`-ladder (not just a `chainLink` chain): consecutive links
are `chainLink`, and `≪` is transitive, so every pair is `≪`. In particular its segments
have pairwise-distinct depths (Lemma 3.1(4)). -/
lemma greedyChain_pairwise_ll (m : Multisegment) :
    (Proof.greedyChain m).val.segments.Pairwise (· ≪ ·) := by
  haveI : Trans (· ≪ ·) (· ≪ ·) (· ≪ ·) := ⟨fun h1 h2 => ll_trans _ _ _ h1 h2⟩
  have h : (Proof.greedyChain m).val.segments.IsChain (· ≪ ·) :=
    (isChain_iff.mp (Proof.greedyChain m).property).imp (fun _ _ hc => hc.1)
  exact h.pairwise

/-- Lex order: `s ≤ t` with equal begins forces `s.b ≤ t.b`. -/
lemma seg_b_le_of_le_of_a_eq {s t : Segment} (h : s ≤ t) (ha : s.a = t.a) : s.b ≤ t.b := by
  rcases (Segment.le_def s t).mp h with h1 | ⟨_, h2⟩
  · have : s.a < t.a := h1
    omega
  · exact h2

/-- `go` only appends, so its result is at least as long as the starting chain. -/
lemma go_length_ge (ms chain : List Segment) (hne : chain ≠ []) :
    chain.length ≤ (extendChain.go ms chain hne).length := by
  induction ms generalizing chain hne with
  | nil => rw [extendChain.go]
  | cons s rest ih =>
    rw [extendChain.go]
    split_ifs with hcl
    · exact le_trans (by simp) (ih (chain ++ [s]) (by simp))
    · exact ih chain hne

/-- **Greedy optimality of `extendChain.go`.** For a sorted list `ms`, if `alt` is any
`isChain` drawn in order from `ms` that validly continues `chain` (its head chain-links
from `chain`'s last element), then greedy produces a result ≥ `chain ++ alt` in length.
The sortedness lets the earlier greedy pick `s` stand in for an alternative's head at the
same begin (patience-sorting: the minimal-end choice never loses). -/
lemma go_optimal : ∀ (ms : List Segment), ms.Pairwise (· ≤ ·) →
    ∀ (chain : List Segment) (hne : chain ≠ []) (alt : List Segment),
      isChain alt → alt <+ ms →
      (∀ h : alt ≠ [], chainLink (chain.getLast hne) (alt.head h)) →
      chain.length + alt.length ≤ (extendChain.go ms chain hne).length := by
  intro ms
  induction ms with
  | nil =>
    intro _ chain hne alt _ hsub _
    rw [List.sublist_nil.mp hsub]; simpa using go_length_ge [] chain hne
  | cons s rest ih =>
    intro hsorted chain hne alt halt hsub hlink
    have hrest_sorted : rest.Pairwise (· ≤ ·) := (List.pairwise_cons.mp hsorted).2
    have hs_le : ∀ a ∈ rest, s ≤ a := (List.pairwise_cons.mp hsorted).1
    rw [extendChain.go]
    cases alt with
    | nil => simpa using go_length_ge (s :: rest) chain hne
    | cons a alt' =>
      have hlink_a : chainLink (chain.getLast hne) a := hlink (by simp)
      have halt' : isChain alt' := by
        rw [isChain_iff, List.isChain_cons] at halt; exact isChain_iff.mpr halt.2
      have hsub' : alt' <+ rest := by
        rcases List.sublist_cons_iff.mp hsub with h | ⟨r, hr, hrs⟩
        · exact (List.sublist_cons_self a alt').trans h
        · obtain ⟨_, rfl⟩ := List.cons.inj hr; exact hrs
      have ha_mem : a ∈ s :: rest := hsub.subset (by simp)
      have hsa_le : s ≤ a := by
        rcases List.mem_cons.mp ha_mem with rfl | h
        · exact le_refl _
        · exact hs_le a h
      split_ifs with hcl
      · have hsa_eq : s.a = a.a := by
          have h1 : s.a = (chain.getLast hne).a + 1 := hcl.2
          have h2 : a.a = (chain.getLast hne).a + 1 := hlink_a.2
          omega
        have hsb_le : s.b ≤ a.b := seg_b_le_of_le_of_a_eq hsa_le hsa_eq
        have hlink' : ∀ h : alt' ≠ [],
            chainLink ((chain ++ [s]).getLast (by simp)) (alt'.head h) := by
          intro h
          cases alt' with
          | nil => exact absurd rfl h
          | cons a2 alt'' =>
            have haa2 : chainLink a a2 := by
              rw [isChain_iff, List.isChain_cons] at halt
              exact halt.1 a2 (by simp)
            have hll : a.a < a2.a ∧ a.b < a2.b := haa2.1
            have haa2a : a2.a = a.a + 1 := haa2.2
            have hgl : (chain ++ [s]).getLast (by simp) = s :=
              List.getLast_append_singleton _
            rw [hgl]
            simp only [List.head_cons]
            refine ⟨⟨?_, ?_⟩, ?_⟩
            · omega
            · omega
            · omega
        have key := ih hrest_sorted (chain ++ [s]) (by simp) alt' halt' hsub' hlink'
        simp only [List.length_append, List.length_cons] at key ⊢
        omega
      · have hane : a ≠ s := by rintro rfl; exact hcl hlink_a
        have hsub_alt : (a :: alt') <+ rest := by
          rcases List.sublist_cons_iff.mp hsub with h | ⟨r, hr, hrs⟩
          · exact h
          · obtain ⟨rfl, _⟩ := List.cons.inj hr; exact absurd rfl hane
        exact ih hrest_sorted chain hne (a :: alt') halt hsub_alt hlink

/-- **Greedy optimality for `Proof.greedyChain`.** Any `isChain` `c` drawn in order from `m`
that starts at `m`'s head is no longer than the leading chain. Hence `Proof.greedyChain m`
realizes the maximal consecutive-begin chain length from `min m` — the reusable half of
Prop 3.3 that both directions of `chainLenPreserved` need. -/
lemma greedyChain_length_ge (m : Multisegment) (c : List Segment)
    (hc : isChain c) (hsub : c <+ m.segments) (hhead : c.head? = m.segments.head?) :
    c.length ≤ (Proof.greedyChain m).val.segments.length := by
  cases c with
  | nil => simp
  | cons x c' =>
    unfold Proof.greedyChain
    split
    · rename_i hseg; rw [hseg] at hsub; exact absurd hsub (by simp)
    · rename_i first rest hseg
      rw [hseg] at hhead hsub
      simp only [List.head?_cons, Option.some.injEq] at hhead; subst hhead
      have hrest_sorted : rest.Pairwise (· ≤ ·) :=
        (List.pairwise_cons.mp (hseg ▸ m.is_sorted)).2
      have hc' : isChain c' := by
        rw [isChain_iff, List.isChain_cons] at hc; exact isChain_iff.mpr hc.2
      have hc'sub : c' <+ rest := by
        rcases List.sublist_cons_iff.mp hsub with h | ⟨r, hr, hrs⟩
        · exact (List.sublist_cons_self x c').trans h
        · obtain ⟨_, rfl⟩ := List.cons.inj hr; exact hrs
      have hlink : ∀ h : c' ≠ [], chainLink (([x]).getLast (by simp)) (c'.head h) := by
        intro h
        cases c' with
        | nil => exact absurd rfl h
        | cons a2 c'' =>
          rw [isChain_iff, List.isChain_cons] at hc
          simpa using hc.1 a2 (by simp)
      have key := go_optimal rest hrest_sorted [x] (by simp) c' hc' hc'sub hlink
      simpa [extendChain, Nat.add_comm] using key

/-- Membership interface for greedy optimality: a chain whose elements all lie in `m` and
whose head is `min m` is no longer than the leading chain. The sublist is recovered from
nodup + sortedness, so callers need only supply membership. -/
lemma greedyChain_length_ge' (m : Multisegment) (c : List Segment)
    (hc : isChain c) (hmem : ∀ x ∈ c, x ∈ m.segments) (hhead : c.head? = m.segments.head?) :
    c.length ≤ (Proof.greedyChain m).val.segments.length := by
  have hlt : c.Pairwise (· < ·) := by
    haveI : Trans (α := Segment) (· < ·) (· < ·) (· < ·) := ⟨lt_trans⟩
    exact ((isChain_iff.mp hc).imp (fun {a b} h => chainLink_imp_lt a b h)).pairwise
  have hnd : c.Nodup := hlt.imp (fun {a b} h => ne_of_lt h)
  have hsub : c <+ m.segments :=
    List.sublist_of_subperm_of_pairwise (List.subperm_of_subset hnd (fun x hx => hmem x hx))
      (isChain_imp_sorted c hc) m.is_sorted
  exact greedyChain_length_ge m c hc hsub hhead

/-- A list with `head? = some sₘ` is `sₘ :: tail`. -/
lemma head?_cons_ex {sₘ : Segment} {l : List Segment} (h : l.head? = some sₘ) :
    ∃ t, l = sₘ :: t := by
  cases hl : l with
  | nil => rw [hl] at h; simp at h
  | cons a t =>
    rw [hl] at h; simp only [List.head?_cons, Option.some.injEq] at h; exact ⟨t, by rw [h]⟩

/-- The head of a sorted multisegment is `≤` every element. -/
lemma head_le_mem (m : Multisegment) (sₘ : Segment) (hsₘ : m.segments.head? = some sₘ)
    (x : Segment) (hx : x ∈ m.segments) : sₘ ≤ x := by
  obtain ⟨t, ht⟩ := head?_cons_ex hsₘ
  rw [ht] at hx
  rcases List.mem_cons.mp hx with rfl | hmem
  · exact le_refl _
  · exact (List.pairwise_cons.mp (ht ▸ m.is_sorted)).1 x hmem

/-- **Begin-based optimality interface.** A chain of `m`-members whose head begins at
`min m` is no longer than the leading chain. The head element itself need not be `m`'s head:
`sₘ` (lex-minimal) is swapped in, and since `sₘ.b ≤` the old head's `b`, the chain survives.
This is the interface the residual-chain construction plugs into. -/
lemma greedyChain_length_ge'' (m : Multisegment) (c : List Segment) (sₘ : Segment)
    (hc : isChain c) (hmem : ∀ x ∈ c, x ∈ m.segments) (hsₘ : m.segments.head? = some sₘ)
    (hbeg : ∀ x, c.head? = some x → x.a = sₘ.a) :
    c.length ≤ (Proof.greedyChain m).val.segments.length := by
  cases c with
  | nil => simp
  | cons x c' =>
    have hxa : x.a = sₘ.a := hbeg x rfl
    obtain ⟨t, ht⟩ := head?_cons_ex hsₘ
    have hsₘm : sₘ ∈ m.segments := ht ▸ List.mem_cons_self
    have hxm : x ∈ m.segments := hmem x (by simp)
    have hsxb : sₘ.b ≤ x.b := seg_b_le_of_le_of_a_eq (head_le_mem m sₘ hsₘ x hxm) hxa.symm
    have hc' : isChain c' := by
      rw [isChain_iff, List.isChain_cons] at hc; exact isChain_iff.mpr hc.2
    have hnew : isChain (sₘ :: c') := by
      rw [isChain_iff, List.isChain_cons]
      refine ⟨?_, isChain_iff.mp hc'⟩
      intro b hb
      rw [isChain_iff, List.isChain_cons] at hc
      have hxb : chainLink x b := hc.1 b hb
      exact ⟨⟨by have := hxb.1.1; omega, by have := hxb.1.2; omega⟩, by have := hxb.2; omega⟩
    have hmem' : ∀ y ∈ (sₘ :: c'), y ∈ m.segments := by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hmy
      · exact hsₘm
      · exact hmem y (by simp [hmy])
    have hhead' : (sₘ :: c').head? = m.segments.head? := by rw [hsₘ]; rfl
    simpa using greedyChain_length_ge' m (sₘ :: c') hnew hmem' hhead'

/-! ## Small order helpers -/

/-- Lex order on segments: `s ≤ t` implies `s.a ≤ t.a`. -/
lemma seg_le_imp_a_le {s t : Segment} (h : s ≤ t) : s.a ≤ t.a := by
  rcases (Segment.le_def s t).mp h with h1 | ⟨h1, _⟩
  · exact le_of_lt h1
  · exact le_of_eq h1

/-- A list whose `head?` is `some x` is `x :: tail`. -/
lemma head?_eq_cons {α : Type*} {l : List α} {x : α} (h : l.head? = some x) :
    l = x :: l.tail := by
  cases l with
  | nil => simp at h
  | cons a t => simp only [List.head?_cons, Option.some.injEq] at h; subst h; rfl

/-- The head's begin is `≤` every segment's begin (sorted ascending). -/
lemma head_begin_le (m : Multisegment) (sₘ : Segment)
    (hsₘ : m.segments.head? = some sₘ) (s : Segment) (hs : s ∈ m.segments) :
    sₘ.a ≤ s.a := by
  have hcons := head?_eq_cons hsₘ
  apply seg_le_imp_a_le
  rw [hcons] at hs
  rcases List.mem_cons.mp hs with rfl | hmem
  · exact le_refl _
  · have hpw := m.is_sorted
    rw [hcons] at hpw
    exact (List.pairwise_cons.mp hpw).1 s hmem


/-! ## Bridging `mw_step` to `Proof.greedyChain` -/

/-- The greedy scan skips the head itself (`¬ chainLink first first`). -/
lemma go_cons_self (first : Segment) (rest : List Segment) :
    extendChain.go (first :: rest) [first] (by simp) =
      extendChain.go rest [first] (by simp) := by
  rw [extendChain.go]
  rw [dif_neg]
  intro h
  exact absurd h.1.1 (lt_irrefl first.a)

/-- `Proof.greedyChain` is the greedy scan of the tail from the singleton head chain. -/
lemma greedyChain_eq_go (m : Multisegment) (first : Segment) (rest : List Segment)
    (hseg : m.segments = first :: rest) :
    (Proof.greedyChain m).val.segments = extendChain.go rest [first] (by simp) := by
  unfold Proof.greedyChain
  split
  · rename_i heq
    rw [hseg] at heq
    simp at heq
  · rename_i f r heq
    rw [hseg] at heq
    obtain ⟨rfl, rfl⟩ := List.cons.inj heq
    rfl

/-- The chain scanned by `mw_step` (full list from the singleton head) is exactly the
leading chain. -/
lemma go_full_eq (m : Multisegment) (x : Segment) (hx : m.segments.head? = some x)
    (hne : [x] ≠ []) :
    extendChain.go m.segments [x] hne = (Proof.greedyChain m).val.segments := by
  have hseg := head?_eq_cons hx
  rw [hseg, go_cons_self x m.segments.tail, greedyChain_eq_go m x m.segments.tail hseg]


/-! ## Layer 1: greedy structure of `extendChain.go` -/

/-- The greedy scan only appends: its result is `chain ++ suffix` with the suffix
drawn from the scanned list. -/
lemma go_prefix (ms chain : List Segment) (hne : chain ≠ []) :
    ∃ suf, extendChain.go ms chain hne = chain ++ suf ∧ ∀ y ∈ suf, y ∈ ms := by
  induction ms generalizing chain hne with
  | nil => exact ⟨[], by rw [extendChain.go]; simp, by simp⟩
  | cons s rest ih =>
    rw [extendChain.go]
    split_ifs with h
    · obtain ⟨suf, heq, hmem⟩ := ih (chain ++ [s]) (by simp)
      refine ⟨s :: suf, by rw [heq]; simp, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy'
      · simp
      · simp [hmem y hy']
    · obtain ⟨suf, heq, hmem⟩ := ih chain hne
      exact ⟨suf, heq, fun y hy => by simp [hmem y hy]⟩

/-- The greedy scan never returns the empty list. -/
lemma go_ne_nil (ms chain : List Segment) (hne : chain ≠ []) :
    extendChain.go ms chain hne ≠ [] := by
  obtain ⟨suf, heq, -⟩ := go_prefix ms chain hne
  rw [heq]
  simp [hne]

/-- The last element of the greedy result is the initial chain's last, or comes from
the scanned list. -/
lemma go_getLast?_cases (ms chain : List Segment) (hne : chain ≠ []) :
    (extendChain.go ms chain hne).getLast? = chain.getLast? ∨
    ∃ y ∈ ms, (extendChain.go ms chain hne).getLast? = some y := by
  induction ms generalizing chain hne with
  | nil => left; rw [extendChain.go]
  | cons s rest ih =>
    rw [extendChain.go]
    split_ifs with h
    · rcases ih (chain ++ [s]) (by simp) with h1 | ⟨y, hy, h2⟩
      · right
        exact ⟨s, by simp, by rw [h1]; simp⟩
      · right
        exact ⟨y, by simp [hy], h2⟩
    · rcases ih chain hne with h1 | ⟨y, hy, h2⟩
      · left; exact h1
      · right; exact ⟨y, by simp [hy], h2⟩

/-- **Maximality of the greedy chain**: no element of the (sorted) scanned list chain-links
from the result's last element. -/
lemma go_last_no_link : ∀ (ms : List Segment), ms.Pairwise (· ≤ ·) →
    ∀ (chain : List Segment) (hne : chain ≠ []),
    ∀ x ∈ ms, ∀ g, (extendChain.go ms chain hne).getLast? = some g →
      ¬ chainLink g x := by
  intro ms
  induction ms with
  | nil => intro _ _ _ x hx; simp at hx
  | cons s rest ih =>
    intro hsorted chain hne x hx g hg hlink
    have hrest_sorted := (List.pairwise_cons.mp hsorted).2
    have hs_le := (List.pairwise_cons.mp hsorted).1
    rw [extendChain.go] at hg
    split_ifs at hg with hcl
    · rcases List.mem_cons.mp hx with hxs | hx'
      · -- x = s; identify g
        have h7 := congrArg Segment.a hxs
        rcases go_getLast?_cases rest (chain ++ [s]) (by simp) with h1 | ⟨y, hy, h2⟩
        · rw [hg] at h1
          have hgs : g = s := by
            rw [List.getLast?_concat] at h1
            exact Option.some.inj h1
          have h8 := congrArg Segment.a hgs
          have h9 := hlink.2
          simp only [] at h7 h8
          omega
        · rw [h2] at hg
          obtain rfl := Option.some.inj hg
          have hle := seg_le_imp_a_le (hs_le y hy)
          have h9 := hlink.2
          simp only [] at h7
          omega
      · exact ih hrest_sorted (chain ++ [s]) (by simp) x hx' g hg hlink
    · rcases List.mem_cons.mp hx with hxs | hx'
      · have h7 := congrArg Segment.a hxs
        rcases go_getLast?_cases rest chain hne with h1 | ⟨y, hy, h2⟩
        · rw [hg] at h1
          have hgl : chain.getLast? = some (chain.getLast hne) :=
            List.getLast?_eq_some_getLast hne
          rw [hgl] at h1
          obtain rfl := Option.some.inj h1
          rw [hxs] at hlink
          exact hcl hlink
        · rw [h2] at hg
          obtain rfl := Option.some.inj hg
          have hle := seg_le_imp_a_le (hs_le y hy)
          have h9 := hlink.2
          simp only [] at h7
          omega
      · exact ih hrest_sorted chain hne x hx' g hg hlink

/-- Index lookup at the split point: the left element. -/
lemma getElem?_split_left {α : Type*} (u v : List α) (σ σ' : α) :
    (u ++ σ :: σ' :: v)[u.length]? = some σ := by
  rw [List.getElem?_append_right (le_refl u.length)]
  simp

/-- Index lookup at the split point: the right element. -/
lemma getElem?_split_right {α : Type*} (u v : List α) (σ σ' : α) :
    (u ++ σ :: σ' :: v)[u.length + 1]? = some σ' := by
  rw [List.getElem?_append_right (by omega : u.length ≤ u.length + 1)]
  simp

/-- **Greedy minimal-end property**: if `(σ, σ')` are consecutive in the greedy result at
a position where `σ'` was appended from the scanned (sorted) list, then any `x` in the
scanned list that chain-links from `σ` has end at least `σ'.b`. -/
lemma go_min_end : ∀ (ms : List Segment), ms.Pairwise (· ≤ ·) →
    ∀ (chain : List Segment) (hne : chain ≠ []) (u v : List Segment) (σ σ' : Segment),
      extendChain.go ms chain hne = u ++ σ :: σ' :: v →
      chain.length ≤ u.length + 1 →
      ∀ x ∈ ms, chainLink σ x → σ'.b ≤ x.b := by
  intro ms
  induction ms with
  | nil =>
    intro _ chain hne u v σ σ' heq hlen x hx
    simp at hx
  | cons s rest ih =>
    intro hsorted chain hne u v σ σ' heq hlen x hx hlink
    have hrest_sorted := (List.pairwise_cons.mp hsorted).2
    have hs_le := (List.pairwise_cons.mp hsorted).1
    have hchainpos : 0 < chain.length := List.length_pos_of_ne_nil hne
    rw [extendChain.go] at heq
    split_ifs at heq with hcl
    · -- s appended: result = go rest (chain ++ [s])
      rcases Nat.lt_or_ge u.length chain.length with hpos | hpos
      · -- boundary pair: u.length + 1 = chain.length, σ = chain.getLast, σ' = s
        obtain ⟨suf, hsuf, -⟩ := go_prefix rest (chain ++ [s]) (by simp)
        have hlists : u ++ σ :: σ' :: v = (chain ++ [s]) ++ suf := heq.symm.trans hsuf
        have hs' : σ' = s := by
          have h0 : (u ++ σ :: σ' :: v)[u.length + 1]?
              = ((chain ++ [s]) ++ suf)[u.length + 1]? := by rw [hlists]
          rw [getElem?_split_right] at h0
          rw [show u.length + 1 = chain.length by omega] at h0
          rw [List.getElem?_append_left (by simp),
            List.getElem?_append_right (le_refl chain.length)] at h0
          simp at h0
          exact h0
        have hσeq : σ = chain.getLast hne := by
          have h0 : (u ++ σ :: σ' :: v)[u.length]?
              = ((chain ++ [s]) ++ suf)[u.length]? := by rw [hlists]
          rw [getElem?_split_left] at h0
          rw [List.getElem?_append_left (by simp; omega),
            List.getElem?_append_left (by omega)] at h0
          have hgl : chain.getLast? = some (chain.getLast hne) :=
            List.getLast?_eq_some_getLast hne
          rw [List.getLast?_eq_getElem?] at hgl
          rw [show u.length = chain.length - 1 by omega, hgl] at h0
          exact Option.some.inj h0
        rcases List.mem_cons.mp hx with hxs | hx'
        · rw [hs', hxs]
        · -- x ∈ rest with x.a = σ.a + 1 = s.a; sorted gives s ≤ x, so s.b ≤ x.b
          have hxa : x.a = s.a := by
            have h1 := hlink.2
            have h2 := hcl.2
            rw [hσeq] at h1
            omega
          have h4 := seg_b_le_of_le_of_a_eq (hs_le x hx') hxa.symm
          rw [hs']
          exact h4
      · -- interior pair: covered by IH on (chain ++ [s]); x = s is vacuous
        rcases List.mem_cons.mp hx with hxs | hx'
        · -- σ sits at index ≥ chain.length in (chain++[s]) ++ suf: σ = s or σ ∈ suf
          obtain ⟨suf, hsuf, hsufmem⟩ := go_prefix rest (chain ++ [s]) (by simp)
          have hlists : u ++ σ :: σ' :: v = (chain ++ [s]) ++ suf := heq.symm.trans hsuf
          have h0 : (u ++ σ :: σ' :: v)[u.length]?
              = ((chain ++ [s]) ++ suf)[u.length]? := by rw [hlists]
          rw [getElem?_split_left, List.append_assoc,
            List.getElem?_append_right (by omega)] at h0
          have hσmem : σ ∈ s :: suf := List.mem_of_getElem? h0.symm
          have hσ_ge : s ≤ σ := by
            rcases List.mem_cons.mp hσmem with heq' | hσ'
            · exact le_of_eq heq'.symm
            · exact hs_le σ (hsufmem σ hσ')
          have h5 := seg_le_imp_a_le hσ_ge
          have h6 := hlink.2
          have h7 := congrArg Segment.a hxs
          simp only [] at h7
          omega
        · exact ih hrest_sorted (chain ++ [s]) (by simp) u v σ σ' heq (by simp; omega)
            x hx' hlink
    · -- s rejected: result = go rest chain
      rcases List.mem_cons.mp hx with hxs | hx'
      · -- x = s: σ = chain.getLast (contradicts rejection) or σ from suf (vacuous)
        obtain ⟨suf, hsuf, hsufmem⟩ := go_prefix rest chain hne
        have hlists : u ++ σ :: σ' :: v = chain ++ suf := heq.symm.trans hsuf
        have h0 : (u ++ σ :: σ' :: v)[u.length]? = (chain ++ suf)[u.length]? := by
          rw [hlists]
        rw [getElem?_split_left] at h0
        rcases Nat.lt_or_ge u.length chain.length with hpos | hpos
        · rw [List.getElem?_append_left hpos] at h0
          have hσlast : σ = chain.getLast hne := by
            have hgl : chain.getLast? = some (chain.getLast hne) :=
              List.getLast?_eq_some_getLast hne
            rw [List.getLast?_eq_getElem?] at hgl
            rw [show u.length = chain.length - 1 by omega, hgl] at h0
            exact Option.some.inj h0
          rw [hxs] at hlink
          rw [hσlast] at hlink
          exact absurd hlink hcl
        · rw [List.getElem?_append_right hpos] at h0
          have hσmem : σ ∈ suf := List.mem_of_getElem? h0.symm
          have hσ_ge : s ≤ σ := hs_le σ (hsufmem σ hσmem)
          have h5 := seg_le_imp_a_le hσ_ge
          have h6 := hlink.2
          have h7 := congrArg Segment.a hxs
          simp only [] at h7
          omega
      · exact ih hrest_sorted chain hne u v σ σ' heq hlen x hx' hlink

/-! ## Layer 2a: leading-chain structure -/

/-- No element of `m` chain-links from the leading chain's last element. -/
lemma greedyChain_last_no_link (m : Multisegment) (x : Segment) (hx : x ∈ m.segments)
    (g : Segment) (hg : (Proof.greedyChain m).val.segments.getLast? = some g) :
    ¬ chainLink g x := by
  intro hlink
  have hm : m.segments ≠ [] := List.ne_nil_of_mem hx
  obtain ⟨first, rest, hseg⟩ := List.exists_cons_of_ne_nil hm
  have hgo := greedyChain_eq_go m first rest hseg
  have hsorted : rest.Pairwise (· ≤ ·) := by
    have h := m.is_sorted; rw [hseg] at h; exact (List.pairwise_cons.mp h).2
  rw [hgo] at hg
  rw [hseg] at hx
  rcases List.mem_cons.mp hx with hxf | hxr
  · have hgC : g ∈ (Proof.greedyChain m).val.segments := by
      rw [hgo]; exact List.mem_of_getLast? hg
    have hgm : g ∈ m.segments := greedyChain_subset m g hgC
    have h1 : first.a ≤ g.a := head_begin_le m first (by rw [hseg]; rfl) g hgm
    have h2 := hlink.2
    have h3 := congrArg Segment.a hxf
    simp only [] at h3
    omega
  · exact go_last_no_link rest hsorted [first] (by simp) x hxr g hg hlink

/-- Greedy minimal-end at leading-chain pairs: the chosen successor has the smallest end
among all valid continuations. -/
lemma greedyChain_min_end (m : Multisegment) (u v : List Segment) (σ σ' : Segment)
    (hsplit : (Proof.greedyChain m).val.segments = u ++ σ :: σ' :: v)
    (x : Segment) (hx : x ∈ m.segments) (hlink : chainLink σ x) : σ'.b ≤ x.b := by
  have hm : m.segments ≠ [] := List.ne_nil_of_mem hx
  obtain ⟨first, rest, hseg⟩ := List.exists_cons_of_ne_nil hm
  have hgo := greedyChain_eq_go m first rest hseg
  have hsorted : rest.Pairwise (· ≤ ·) := by
    have h := m.is_sorted; rw [hseg] at h; exact (List.pairwise_cons.mp h).2
  have hsplit' : extendChain.go rest [first] (by simp) = u ++ σ :: σ' :: v := by
    rw [← hgo]; exact hsplit
  rw [hseg] at hx
  rcases List.mem_cons.mp hx with hxf | hxr
  · have hσC : σ ∈ (Proof.greedyChain m).val.segments := by rw [hsplit]; simp
    have hσm := greedyChain_subset m σ hσC
    have h1 : first.a ≤ σ.a := head_begin_le m first (by rw [hseg]; rfl) σ hσm
    have h2 := hlink.2
    have h3 := congrArg Segment.a hxf
    simp only [] at h3
    omega
  · exact go_min_end rest hsorted [first] (by simp) u v σ σ' hsplit' (by simp) x hxr hlink

/-- A leading-chain element with a valid continuation in `m` has a successor in the
chain: it is not the last element. -/
lemma greedyChain_succ_split (m : Multisegment) (σ : Segment)
    (hσ : σ ∈ (Proof.greedyChain m).val.segments)
    (z : Segment) (hz : z ∈ m.segments) (hlink : chainLink σ z) :
    ∃ u σ' v, (Proof.greedyChain m).val.segments = u ++ σ :: σ' :: v := by
  obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem hσ
  cases l₂ with
  | nil =>
    exfalso
    have hlast : (Proof.greedyChain m).val.segments.getLast? = some σ := by
      rw [hsplit, List.getLast?_concat]
    exact greedyChain_last_no_link m z hz σ hlast hlink
  | cons σ' l₂' => exact ⟨l₁, σ', l₂', hsplit⟩

/-- Consecutive leading-chain elements are chain-linked. -/
lemma greedyChain_consecutive_link (m : Multisegment) (u v : List Segment) (σ σ' : Segment)
    (hsplit : (Proof.greedyChain m).val.segments = u ++ σ :: σ' :: v) :
    chainLink σ σ' := by
  have hchain : isChain (Proof.greedyChain m).val.segments := (Proof.greedyChain m).property
  rw [isChain_iff, hsplit] at hchain
  exact (List.isChain_append_cons_cons.mp hchain).2.1


/-! ## Leading sequences: the greedy chain is the only one

A list `c` of segments is *leading* when it satisfies the paper's (a)–(c): it starts at the
least segment of `m`, each element is followed by the least segment chain-linked to it, and its
last element has no chain-link. The greedy scan is leading (`greedy_isLeading`), any two leading
lists are equal (`isLeading_unique`), and a sequence of indices is in `leadingIndices m` exactly
when the segments at its positions form a leading list (`isLeading_segsAt_iff`). Hence every
sequence of leading indices gives the greedy chain (`segments_of_leadingIndices`), and the
positions of the greedy chain are one such sequence (`greedyIdx_mem_leadingIndices`). -/

private def IsLeading (m : Multisegment) (c : List Segment) : Prop :=
  c ≠ [] ∧
  (∀ x, c.head? = some x → isFirst m x) ∧
  (∀ n (hn : n + 1 < c.length), isNext m c[n] c[n + 1]) ∧
  (∀ x, c.getLast? = some x → isLast m x)

/-- The segments at the positions `i`. -/
private def segsAt (m : Multisegment) (i : List ℕ) (H : ∀ j ∈ i, j < m.segments.length) :
    List Segment :=
  i.attach.map fun ⟨j, hj⟩ => m.segments[j]'(H j hj)

private lemma length_segsAt (m : Multisegment) (i : List ℕ) (H : ∀ j ∈ i, j < m.segments.length) :
    (segsAt m i H).length = i.length := by
  simp [segsAt]

private lemma getElem_segsAt (m : Multisegment) (i : List ℕ) (H : ∀ j ∈ i, j < m.segments.length)
    (n : ℕ) (hn : n < i.length) :
    (segsAt m i H)[n]'(by rw [length_segsAt]; exact hn) =
      m.segments[i[n]]'(H _ (List.getElem_mem hn)) := by
  simp [segsAt]

lemma lt_length_of_mem_leadingIndices {m : Multisegment} {i : List ℕ} {j : ℕ}
    (hj : j ∈ i) (hi : i ∈ leadingIndices m) : j < m.segments.length := by
  obtain ⟨⟨k, ⟨-, -, hb⟩, -⟩, -⟩ := hi
  exact hb j hj

private lemma greedy_isLeading (m : Multisegment) (hm : m.segments ≠ []) :
    IsLeading m (Proof.greedyChain m).val.segments := by
  obtain ⟨first, rest, hseg⟩ := List.exists_cons_of_ne_nil hm
  have hhead : (Proof.greedyChain m).val.segments.head? = some first :=
    greedyChain_head m first (by rw [hseg]; rfl)
  refine ⟨ne_nil_of_head?_eq_some hhead, ?_, ?_, ?_⟩
  · intro x hx
    rw [hhead] at hx
    obtain rfl := Option.some.inj hx
    refine ⟨by rw [hseg]; exact List.mem_cons_self, ?_⟩
    intro y hy
    exact head_le_mem m first (by rw [hseg]; rfl) y hy
  · intro n hn
    have hsplit : (Proof.greedyChain m).val.segments =
        (Proof.greedyChain m).val.segments.take n ++ (Proof.greedyChain m).val.segments[n] ::
          (Proof.greedyChain m).val.segments[n + 1] ::
            (Proof.greedyChain m).val.segments.drop (n + 2) := by
      conv_lhs => rw [← List.take_append_drop n (Proof.greedyChain m).val.segments]
      rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]
    have hlink := greedyChain_consecutive_link m _ _ _ _ hsplit
    refine ⟨greedyChain_subset m _ (List.getElem_mem _), hlink, ?_⟩
    intro x hx hxl
    have hb := greedyChain_min_end m _ _ _ _ hsplit x hx hxl
    have ha : ((Proof.greedyChain m).val.segments[n + 1]).a = x.a := by
      have := hlink.2; have := hxl.2; omega
    exact (Segment.le_def _ _).mpr (Or.inr ⟨ha, hb⟩)
  · intro x hx t ht
    exact greedyChain_last_no_link m t ht x hx

private lemma isNext_unique {m : Multisegment} {s t t' : Segment}
    (h : isNext m s t) (h' : isNext m s t') : t = t' :=
  le_antisymm (h.2.2 t' h'.1 h'.2.1) (h'.2.2 t h.1 h.2.1)

private lemma isLeading_getElem_eq (m : Multisegment) {c c' : List Segment}
    (hc : IsLeading m c) (hc' : IsLeading m c') :
    ∀ n (hn : n < c.length) (hn' : n < c'.length), c[n] = c'[n] := by
  intro n
  induction n with
  | zero =>
    intro hn hn'
    have h1 := hc.2.1 c[0] (by rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hn])
    have h2 := hc'.2.1 c'[0] (by rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hn'])
    exact le_antisymm (h1.2 _ h2.1) (h2.2 _ h1.1)
  | succ n ih =>
    intro hn hn'
    have h1 := hc.2.2.1 n hn
    have h2 := hc'.2.2.1 n hn'
    rw [ih (by omega) (by omega)] at h1
    exact isNext_unique h1 h2

private lemma isLeading_not_lt (m : Multisegment) {c c' : List Segment}
    (hc : IsLeading m c) (hc' : IsLeading m c') : ¬ c.length < c'.length := by
  intro hlt
  have hpos : 0 < c.length := List.length_pos_of_ne_nil hc.1
  have hlast := hc.2.2.2 (c[c.length - 1]'(by omega))
    (by rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)])
  have hnext := hc'.2.2.1 (c.length - 1) (by omega)
  have heq := isLeading_getElem_eq m hc hc' (c.length - 1) (by omega) (by omega)
  rw [← heq] at hnext
  obtain ⟨hmem, hlink, -⟩ := hnext
  exact hlast _ hmem hlink

private lemma isLeading_unique (m : Multisegment) {c c' : List Segment}
    (hc : IsLeading m c) (hc' : IsLeading m c') : c = c' := by
  have hlen : c.length = c'.length := by
    have h1 := isLeading_not_lt m hc hc'
    have h2 := isLeading_not_lt m hc' hc
    omega
  exact List.ext_getElem hlen (isLeading_getElem_eq m hc hc')

private lemma isLeading_segsAt_iff (m : Multisegment) (i : List ℕ)
    (H : ∀ j ∈ i, j < m.segments.length) :
    i ∈ leadingIndices m ↔ i.Nodup ∧ IsLeading m (segsAt m i H) := by
  constructor
  · rintro ⟨⟨k, hk⟩, ha, hb, hc⟩
    have hidx : i.length = k ∧ i.Nodup ∧ ∀ j ∈ i, j < m.segments.length := hk.1
    obtain ⟨hlen, hnd, -⟩ := hidx
    have hpos : 0 < i.length := by have := hk.2; omega
    refine ⟨hnd, ?_, ?_, ?_, ?_⟩
    · rw [← List.length_pos_iff_ne_nil, length_segsAt]; exact hpos
    · intro x hx
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by rw [length_segsAt]; exact hpos),
        getElem_segsAt m i H 0 hpos] at hx
      exact (Option.some.inj hx) ▸ ha
    · intro n hn
      rw [length_segsAt] at hn
      rw [getElem_segsAt m i H n (by omega), getElem_segsAt m i H (n + 1) hn]
      exact hb n (by change n + 1 < k; omega)
    · intro x hx
      rw [List.getLast?_eq_getElem?, length_segsAt,
        List.getElem?_eq_getElem (by rw [length_segsAt]; omega),
        getElem_segsAt m i H (i.length - 1) (by omega)] at hx
      exact (Option.some.inj hx) ▸ hc (i.length - 1) (by change i.length - 1 + 1 = k; omega)
  · rintro ⟨hnd, hne, ha, hb, hc⟩
    have hpos : 0 < i.length := by
      rw [← length_segsAt m i H]; exact List.length_pos_of_ne_nil hne
    refine ⟨⟨i.length, ⟨rfl, hnd, H⟩, hpos⟩, ?_, ?_, ?_⟩
    · have := ha ((segsAt m i H)[0]'(by rw [length_segsAt]; exact hpos))
        (by rw [List.head?_eq_getElem?, List.getElem?_eq_getElem])
      rwa [getElem_segsAt m i H 0 hpos] at this
    · intro j hj
      change j + 1 < i.length at hj
      have := hb j (by rw [length_segsAt]; exact hj)
      rwa [getElem_segsAt m i H j (by omega), getElem_segsAt m i H (j + 1) hj] at this
    · intro j hj
      change j + 1 = i.length at hj
      have hj' : j < (segsAt m i H).length := by rw [length_segsAt]; omega
      have := hc ((segsAt m i H)[j]'hj')
        (by rw [List.getLast?_eq_getElem?,
              show (segsAt m i H).length - 1 = j by rw [length_segsAt]; omega]
            exact List.getElem?_eq_getElem hj')
      rwa [getElem_segsAt m i H j (by omega)] at this

/-- Every sequence of leading indices gives the segments of the greedy chain (paper: the set of
leading segments depends only on `m`). -/
private lemma segsAt_eq_segments (m : Multisegment) {i : List ℕ} (hi : i ∈ leadingIndices m)
    (H : ∀ j ∈ i, j < m.segments.length) :
    segsAt m i H = (Proof.greedyChain m).val.segments := by
  have hm : m.segments ≠ [] := by
    obtain ⟨⟨k, ⟨hlen, -, -⟩, hk⟩, -⟩ := hi
    obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil i (List.ne_nil_of_length_pos (by omega))
    exact List.ne_nil_of_length_pos (by have := H j hj; omega)
  exact isLeading_unique m ((isLeading_segsAt_iff m i H).mp hi).2 (greedy_isLeading m hm)

/-- The positions of the greedy chain's segments. -/
private def greedyIdx (m : Multisegment) : List ℕ :=
  (Proof.greedyChain m).val.segments.map (fun x => List.idxOf x m.segments)

private lemma greedy_nodup (m : Multisegment) : (Proof.greedyChain m).val.segments.Nodup :=
  (greedyChain_pairwise_ll m).imp fun h heq => by subst heq; exact lt_irrefl _ h.1

private lemma greedyIdx_bound (m : Multisegment) : ∀ j ∈ greedyIdx m, j < m.segments.length := by
  intro j hj
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hj
  exact List.idxOf_lt_length_iff.mpr (greedyChain_subset m x hx)

private lemma segsAt_greedyIdx (m : Multisegment) :
    segsAt m (greedyIdx m) (greedyIdx_bound m) = (Proof.greedyChain m).val.segments := by
  apply List.ext_getElem
  · simp [segsAt, greedyIdx]
  · intro n h1 h2
    simp [segsAt, greedyIdx, List.getElem_idxOf]

lemma greedyIdx_mem_leadingIndices (m : Multisegment) (hm : m.segments ≠ []) :
    greedyIdx m ∈ leadingIndices m := by
  rw [isLeading_segsAt_iff m _ (greedyIdx_bound m)]
  refine ⟨?_, ?_⟩
  · exact (greedy_nodup m).map_on fun x hx y _ hxy =>
      (List.idxOf_inj (greedyChain_subset m x hx)).mp hxy
  · rw [segsAt_greedyIdx]; exact greedy_isLeading m hm

lemma leadingIndices_nonempty (m : Multisegment) (hm : m.segments ≠ []) :
    (leadingIndices m).Nonempty :=
  ⟨greedyIdx m, greedyIdx_mem_leadingIndices m hm⟩

/-! ## `leadingIndices m` is finite (and computable) -/

/-- All lists of distinct positions in `m`: the permutations of the sublists of `0, …, n − 1`. -/
private def candidates (m : Multisegment) : List (List ℕ) :=
  (List.range m.segments.length).sublists.flatMap List.permutations

private lemma mem_candidates {m : Multisegment} {i : List ℕ} :
    i ∈ candidates m ↔ i.Nodup ∧ ∀ j ∈ i, j < m.segments.length := by
  constructor
  · intro h
    obtain ⟨s, hs, hperm⟩ := List.mem_flatMap.mp h
    rw [List.mem_sublists] at hs
    rw [List.mem_permutations] at hperm
    exact ⟨hperm.nodup_iff.mpr (hs.nodup List.nodup_range),
      fun j hj => List.mem_range.mp (hs.subset (hperm.subset hj))⟩
  · rintro ⟨hnd, hb⟩
    refine List.mem_flatMap.mpr
      ⟨(List.range m.segments.length).filter (fun a => decide (a ∈ i)),
        List.mem_sublists.mpr List.filter_sublist, ?_⟩
    rw [List.mem_permutations]
    refine (List.perm_ext_iff_of_nodup hnd (List.nodup_range.filter _)).mpr fun a => ?_
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun ha => ⟨hb a ha, ha⟩, fun h => h.2⟩

private lemma map_getElem?_eq_iff (m : Multisegment) (i : List ℕ)
    (H : ∀ j ∈ i, j < m.segments.length) (g : List Segment) :
    i.map (fun j => m.segments[j]?) = g.map some ↔ segsAt m i H = g := by
  constructor
  · intro h
    have hlen : i.length = g.length := by
      have := congrArg List.length h; simpa using this
    apply List.ext_getElem
    · rw [length_segsAt]; exact hlen
    · intro n hn hn'
      rw [length_segsAt] at hn
      have := congrArg (fun l => l[n]?) h
      simp only [List.getElem?_map, List.getElem?_eq_getElem hn, List.getElem?_eq_getElem hn',
        Option.map_some, Option.some.injEq] at this
      rw [getElem_segsAt m i H n hn]
      exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans this)
  · intro h
    apply List.ext_getElem?
    intro n
    simp only [List.getElem?_map]
    by_cases hn : n < i.length
    · have hn' : n < g.length := by rw [← h, length_segsAt]; exact hn
      rw [List.getElem?_eq_getElem hn, List.getElem?_eq_getElem hn']
      simp only [Option.map_some, Option.some.injEq]
      rw [List.getElem_of_eq h.symm hn', getElem_segsAt m i H n hn]
      exact List.getElem?_eq_getElem _
    · rw [List.getElem?_eq_none (by omega),
        List.getElem?_eq_none (by rw [← h, length_segsAt]; omega)]
      rfl

/-- `leadingIndices m` is finite: the leading candidates. -/
-- A `Fintype` instance, not a `Decidable` one: it carries a computed list. Allowed in a `_u`
-- file because any two such instances agree, but it may be a little dangerous — to be checked
-- (see TODO.md).
instance (m : Multisegment) : Fintype (leadingIndices m) :=
  Fintype.ofFinset
    (((candidates m).filter fun i => decide (i ≠ [] ∧
        i.map (fun j => m.segments[j]?) = (Proof.greedyChain m).val.segments.map some)).toFinset)
    (fun i => by
      simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, mem_candidates]
      constructor
      · rintro ⟨⟨hnd, hb⟩, hne, hmap⟩
        rw [map_getElem?_eq_iff m i hb] at hmap
        rw [isLeading_segsAt_iff m i hb, hmap]
        refine ⟨hnd, greedy_isLeading m ?_⟩
        obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil i hne
        exact List.ne_nil_of_length_pos (by have := hb j hj; omega)
      · intro hi
        have hb : ∀ j ∈ i, j < m.segments.length := fun j hj =>
          lt_length_of_mem_leadingIndices hj hi
        obtain ⟨hnd, hne, -⟩ := (isLeading_segsAt_iff m i hb).mp hi
        refine ⟨⟨hnd, hb⟩, ?_, ?_⟩
        · intro h; subst h; exact hne rfl
        · rw [map_getElem?_eq_iff m i hb]
          exact segsAt_eq_segments m hi hb)

/-- Membership in `leadingIndices` is decided through its finite set. -/
instance (m : Multisegment) (i : List ℕ) : Decidable (i ∈ leadingIndices m) :=
  decidable_of_iff (i ∈ (leadingIndices m).toFinset) Set.mem_toFinset

-- The index rule learns it: `m.segments[j]` is valid for `j ∈ i` with `i ∈ leadingIndices m`.
attribute [grind →] lt_length_of_mem_leadingIndices

/-- Every sequence of leading indices gives the segments of the greedy chain (paper: the set of
leading segments depends only on `m`). -/
lemma segments_of_leadingIndices (m : Multisegment) {i : List ℕ} (hi : i ∈ leadingIndices m) :
    [m.segments[j] | j ∈ i] = (Proof.greedyChain m).val.segments :=
  segsAt_eq_segments m hi (fun _ hj => lt_length_of_mem_leadingIndices hj hi)

/-- The segments at a sequence of leading indices do not depend on the sequence: this is what
makes `let i ∈ leadingIndices m; [m.segments[j] | j ∈ i]` well defined. -/
lemma leading_segments_indep (m : Multisegment) :
    ∀ x (hx : x ∈ leadingIndices m) y (hy : y ∈ leadingIndices m),
      [m.segments[j] | j ∈ x] = [m.segments[j] | j ∈ y] := by
  intro x hx y hy
  exact (segments_of_leadingIndices m hx).trans (segments_of_leadingIndices m hy).symm

attribute [grind →] leading_segments_indep

-- `let i ∈ leadingIndices m; …` needs the set nonempty, which follows from `m.segments ≠ []`.
attribute [grind ←] leadingIndices_nonempty

/-! ## The MW step by indices equals the computation along the greedy chain -/

@[grind →] lemma length_pos_of_mem_leadingIndices {m : Multisegment} {x : List ℕ}
    (hx : x ∈ leadingIndices m) : 0 < x.length := by
  obtain ⟨⟨k, hk⟩, -⟩ := hx
  have hidx : x.length = k ∧ x.Nodup ∧ ∀ j ∈ x, j < m.segments.length := hk.1
  have := hk.2
  omega

/-- Conversely to `leadingIndices_nonempty`: a sequence of leading indices points into `m`,
so `m` is nonempty. -/
lemma ne_nil_of_leadingIndices_nonempty {m : Multisegment} (h : (leadingIndices m).Nonempty) :
    m.segments ≠ [] := by
  obtain ⟨x, hx⟩ := h
  have := lt_length_of_mem_leadingIndices
    (List.getElem_mem (length_pos_of_mem_leadingIndices hx)) hx
  exact List.ne_nil_of_length_pos (by omega)

/-- `(leadingIndices m).Nonempty` is decided by `m.segments ≠ []` (for `decide` on examples). -/
instance (m : Multisegment) : Decidable (leadingIndices m).Nonempty :=
  decidable_of_iff (m.segments ≠ [])
    ⟨leadingIndices_nonempty m, ne_nil_of_leadingIndices_nonempty⟩

/-- The first leading index points at the least segment, the head of `m`. -/
lemma getElem_zero_eq_head {m : Multisegment} (hm : m.segments ≠ []) {x : List ℕ}
    (hx : x ∈ leadingIndices m) : m.segments[x[0]] = m.segments.head hm := by
  obtain ⟨⟨k, hk⟩, ha, -, -⟩ := hx
  exact le_antisymm (ha.2 _ (List.head_mem hm))
    (head_le_mem m _ (List.head?_eq_some_head hm) _ ha.1)

lemma length_eq_greedy {m : Multisegment} {x : List ℕ} (hx : x ∈ leadingIndices m) :
    x.length = (Proof.greedyChain m).val.segments.length := by
  have := congrArg List.length (segments_of_leadingIndices m hx)
  simpa using this

/-- Along a sequence of leading indices the begins increase, so `[b(Δ_{i₁}), b(Δ_{i_k})]` is a
segment. -/
lemma a_le_a_last {m : Multisegment} {x : List ℕ} (hx : x ∈ leadingIndices m) :
    m.segments[x[0]].a ≤ m.segments[x[x.length - 1]].a := by
  have H : ∀ j ∈ x, j < m.segments.length := fun _ hj => lt_length_of_mem_leadingIndices hj hx
  have hseg := segsAt_eq_segments m hx H
  have hpos := length_pos_of_mem_leadingIndices hx
  have hpw : (segsAt m x H).Pairwise (· ≪ ·) := by rw [hseg]; exact greedyChain_pairwise_ll m
  rw [← getElem_segsAt m x H 0 hpos, ← getElem_segsAt m x H (x.length - 1) (by omega)]
  rcases Nat.eq_zero_or_pos (x.length - 1) with h1 | h1
  · simp only [h1, le_refl]
  · exact le_of_lt (List.pairwise_iff_getElem.mp hpw 0 (x.length - 1)
      (by rw [length_segsAt]; omega) (by rw [length_segsAt]; omega) h1).1

attribute [grind →] a_le_a_last

/-- The begin of the last leading segment: `min m + k − 1` (the chain's begins are consecutive). -/
lemma a_last_eq {m : Multisegment} (hm : m.segments ≠ []) {x : List ℕ}
    (hx : x ∈ leadingIndices m) :
    m.segments[x[x.length - 1]].a
      = (m.segments.head hm).a + ↑((Proof.greedyChain m).val.segments.length - 1) := by
  have H : ∀ j ∈ x, j < m.segments.length := fun _ hj => lt_length_of_mem_leadingIndices hj hx
  have hseg := segsAt_eq_segments m hx H
  have hpos := length_pos_of_mem_leadingIndices hx
  have hk := length_eq_greedy hx
  rw [← getElem_segsAt m x H _ (by omega), List.getElem_of_eq hseg]
  have h0 : (Proof.greedyChain m).val.segments[0]? = some (m.segments.head hm) := by
    rw [← List.head?_eq_getElem?]
    exact greedyChain_head m _ (List.head?_eq_some_head hm)
  have ht := List.getElem?_eq_getElem (l := (Proof.greedyChain m).val.segments) (i := x.length - 1)
    (by rw [← hk]; omega)
  rw [chain_get_a _ (Proof.greedyChain m).property (x.length - 1) _ _ h0 ht, hk]

-- The statement mirrors the `_t` term of `makeResidual` (`segmentResidual` under the condition
-- `a < b`), so it is read with the fundamental rule on, exactly as in `MW2_t`.
set_option autoProp.rule true in
/-- Paper: `m^MW = Σ Δ_i^*` — the segments at the positions outside `x`, and `⁻Δ` at the
positions in `x` (dropped when empty) — is the residual along the greedy chain. -/
lemma residual_eq (m : Multisegment) {x : List ℕ} (hx : x ∈ leadingIndices m) :
    (([m.segments[j] | j < m.segments.length, j ∉ x] ++
        [segmentResidual m.segments[j] | j ∈ x, m.segments[j].a < m.segments[j].b]
        : List Segment) : Multisegment)
      = Proof.residualAlong m (Proof.greedyChain m).val.segments := by
  have H : ∀ j ∈ x, j < m.segments.length := fun _ hj => lt_length_of_mem_leadingIndices hj hx
  have hseg : segsAt m x H = (Proof.greedyChain m).val.segments := segsAt_eq_segments m hx H
  have hnd : x.Nodup := ((isLeading_segsAt_iff m x H).mp hx).1
  -- the residuals of the leading segments
  have hB : [segmentResidual m.segments[j] | j ∈ x, m.segments[j].a < m.segments[j].b]
      = (Proof.greedyChain m).val.segments.filterMap Proof.shorten := by
    rw [← hseg]
    unfold segsAt
    rw [List.filterMap_map, filterMap_eq_flatMap_toList]
    congr 1
    funext ⟨j, hj⟩
    by_cases hlt : m.segments[j].a < m.segments[j].b
    · simp [Proof.shorten, hlt]
    · simp [Proof.shorten, hlt]
  -- the other segments, as a multiset: `m` minus the leading segments
  have hA : [m.segments[j] | j < m.segments.length, j ∉ x]
      ~ (Proof.greedyChain m).val.segments.foldl List.erase m.segments := by
    rw [← hseg]
    apply perm_foldl_erase_of_perm_append
    have hA' := comprehension_cond (List.range m.segments.length) (fun j => j ∉ x)
      (fun j hj _ => m.segments[j]'(List.mem_range.mp hj)) _ rfl
    rw [hA']
    unfold segsAt
    have hperm : (List.range m.segments.length).filter (fun j => decide (j ∉ x)) ++ x
        ~ List.range m.segments.length := by
      refine (List.Perm.append_left _ ?_).trans
        (List.filter_append_perm (fun j => decide (j ∉ x)) (List.range m.segments.length))
      refine (List.perm_ext_iff_of_nodup hnd (List.nodup_range.filter _)).mpr fun j => ?_
      simp only [List.mem_filter, List.mem_range, Bool.not_eq_true', decide_eq_false_iff_not,
        not_not]
      exact ⟨fun hj => ⟨H j hj, hj⟩, fun h => h.2⟩
    have hall : ∀ j ∈ (List.range m.segments.length).filter (fun j => decide (j ∉ x)) ++ x,
        j < m.segments.length := by
      intro j hj
      rcases List.mem_append.mp hj with h | h
      · exact List.mem_range.mp (List.mem_of_mem_filter h)
      · exact H j h
    have key : List.pmap (fun (j : ℕ) (hj : j < m.segments.length) => m.segments[j])
        ((List.range m.segments.length).filter (fun j => decide (j ∉ x)) ++ x) hall
        ~ m.segments :=
      (List.Perm.pmap _ hperm).trans (by rw [pmap_range_getElem])
    rw [List.pmap_append, List.pmap_eq_map_attach, List.pmap_eq_map_attach] at key
    exact key
  -- both multisegments are the sorted versions of permuted lists
  unfold Proof.residualAlong
  show (⟨_, _⟩ : Multisegment) = ⟨_, _⟩
  congr 1
  refine List.Perm.eq_of_pairwise (le := (· ≤ ·)) ?_ ?_ ?_ ?_
  · intro a b _ _ h₁ h₂; exact le_antisymm h₁ h₂
  · exact List.pairwise_insertionSort _ _
  · exact List.pairwise_insertionSort _ _
  · have hB' : [segmentResidual m.segments[j] | j ∈ x, m.segments[j].a < m.segments[j].b]
        ~ (Proof.greedyChain m).val.segments.filterMap Proof.shorten := by
      rw [hB]
    exact (List.perm_insertionSort _ _).trans
      ((hA.append hB').trans (List.perm_insertionSort _ _).symm)

set_option autoProp.rule true in
/-- `m^MW` does not depend on the sequence of leading indices: this is what makes
`let i ∈ leadingIndices m; …` in `makeResidual` well defined. -/
lemma residual_indep (m : Multisegment) :
    ∀ x (hx : x ∈ leadingIndices m) y (hy : y ∈ leadingIndices m),
      (([m.segments[j] | j < m.segments.length, j ∉ x]
        ++ [segmentResidual m.segments[j] | j ∈ x, m.segments[j].a < m.segments[j].b]
        : List Segment) : Multisegment)
      = (([m.segments[j] | j < m.segments.length, j ∉ y]
        ++ [segmentResidual m.segments[j] | j ∈ y, m.segments[j].a < m.segments[j].b]
        : List Segment) : Multisegment) := by
  intro x hx y hy
  exact (residual_eq m hx).trans (residual_eq m hy).symm

/-- `Δ^MW(m)` does not depend on the sequence of leading indices either. -/
lemma deltaCirc_indep (m : Multisegment) :
    ∀ x (hx : x ∈ leadingIndices m) y (hy : y ∈ leadingIndices m),
      Segment m.segments[x[0]].a m.segments[x[x.length - 1]].a
        = Segment m.segments[y[0]].a m.segments[y[y.length - 1]].a := by
  intro x hx y hy
  have hm : m.segments ≠ [] := List.ne_nil_of_length_pos (by
    have := lt_length_of_mem_leadingIndices
      (List.getElem_mem (length_pos_of_mem_leadingIndices hx)) hx
    omega)
  have h0 : m.segments[x[0]] = m.segments[y[0]] := by
    rw [getElem_zero_eq_head hm hx, getElem_zero_eq_head hm hy]
  have hlen : x.length = y.length := by rw [length_eq_greedy hx, length_eq_greedy hy]
  have Hx : ∀ j ∈ x, j < m.segments.length := fun _ hj => lt_length_of_mem_leadingIndices hj hx
  have Hy : ∀ j ∈ y, j < m.segments.length := fun _ hj => lt_length_of_mem_leadingIndices hj hy
  have hL : m.segments[x[x.length - 1]] = m.segments[y[y.length - 1]] := by
    rw [← getElem_segsAt m x Hx _ (by have := length_pos_of_mem_leadingIndices hx; omega),
      ← getElem_segsAt m y Hy _ (by have := length_pos_of_mem_leadingIndices hy; omega),
      List.getElem_of_eq (segsAt_eq_segments m hx Hx),
      List.getElem_of_eq (segsAt_eq_segments m hy Hy)]
    simp only [hlen]
  exact Segment.ext_ab (by change m.segments[x[0]].a = m.segments[y[0]].a; rw [h0])
    (by change m.segments[x[x.length - 1]].a = m.segments[y[y.length - 1]].a; rw [hL])

attribute [grind →] residual_indep deltaCirc_indep
