import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.MW_t
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Chain

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.style.show false
set_option linter.hashCommand false

open scoped List

/-!
# Mœglin–Waldspurger Algorithm — proofs

Decidability, chain-preservation of the greedy scan, its proof-carrying
packagings (`extendChain`, `leadingChain`, `mwStep`), and the greedy-optimality
API consumed by `chainLenPreserved` (Prop 3.3).
-/

namespace MW


instance : ∀ l, Decidable (isChain l) := by
  intro l; unfold isChain; infer_instance

/-- A `chainLink` between two segments implies strict lex order. -/
lemma chainLink_imp_lt (s₁ s₂ : Segment) (h : chainLink s₁ s₂) : s₁ < s₂ :=
  Prod.Lex.left _ _ h.1.1

/-- An `isChain` list is also lex-sorted under `≤`. -/
lemma isChain_imp_sorted (l : List Segment) (h : isChain l) : l.Pairwise (· ≤ ·) := by
  have h_lt : l.IsChain (· < ·) := h.imp chainLink_imp_lt
  exact h_lt.pairwise.imp le_of_lt

/-- Snoc preserves `isChain` when the new last element has a `chainLink` from the
    previous last. -/
lemma isChain_snoc (l : List Segment) (hne : l ≠ [])
    (h : isChain l) (x : Segment) (h_link : chainLink (l.getLast hne) x) :
    isChain (l ++ [x]) := by
  apply List.IsChain.append h (List.IsChain.singleton x)
  intros a ha b hb
  rw [List.getLast?_eq_some_getLast hne] at ha
  simp at ha hb
  subst ha; subst hb
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

/-- The leading chain of `m`: starts from the minimum segment and greedily
    extends as far as possible through the sorted list. -/
def leadingChain (m : Multisegment) : Chain :=
  match h : m.segments with
  | []            => ⟨⟨[], by simp⟩, by simp [isChain]⟩
  | first :: rest =>
    extendChain
      ⟨rest, (List.pairwise_cons.mp (h ▸ m.is_sorted)).2⟩
      -- the singleton chain `[first]` is vacuously a chain
      ⟨⟨[first], by simp⟩, by simp [isChain]⟩
      (by simp)

/-! ## Downstream API

These lemmas are not used elsewhere in this file. They record facts that are true of the
definitions above (`isChain`, `extendChain`, `leadingChain`) for the benefit of consumers
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
      rw [isChain, List.isChain_cons] at h
      obtain ⟨hlink, htail⟩ := h
      cases xs with
      | nil => simp at hi
      | cons y ys =>
        have hya : y.a = x.a + 1 := (hlink y (by simp)).2
        have hrec := ih htail j y t (by simp) hi
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
lemma leadingChain_subset (m : Multisegment) (x : Segment)
    (hx : x ∈ (leadingChain m).val.segments) : x ∈ m.segments := by
  unfold leadingChain at hx
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
lemma leadingChain_head (m : Multisegment) (sₘ : Segment) (h : m.segments.head? = some sₘ) :
    (leadingChain m).val.segments.head? = some sₘ := by
  unfold leadingChain
  split
  · rename_i heq; rw [heq] at h; simp at h
  · rename_i first rest heq
    rw [heq] at h; simp only [List.head?_cons, Option.some.injEq] at h
    simp only [extendChain, extendChain.go_head, List.head?_cons]; rw [h]

/-- The leading chain is a `≪`-ladder (not just a `chainLink` chain): consecutive links
are `chainLink`, and `≪` is transitive, so every pair is `≪`. In particular its segments
have pairwise-distinct depths (Lemma 3.1(4)). -/
lemma leadingChain_pairwise_ll (m : Multisegment) :
    (leadingChain m).val.segments.Pairwise (· ≪ ·) := by
  haveI : Trans (· ≪ ·) (· ≪ ·) (· ≪ ·) := ⟨fun h1 h2 => ll_trans _ _ _ h1 h2⟩
  have h : (leadingChain m).val.segments.IsChain (· ≪ ·) :=
    (leadingChain m).property.imp (fun _ _ hc => hc.1)
  exact h.pairwise

/-- Lex order: `s ≤ t` with equal begins forces `s.b ≤ t.b`. -/
lemma seg_b_le_of_le_of_a_eq {s t : Segment} (h : s ≤ t) (ha : s.a = t.a) : s.b ≤ t.b := by
  have h' : toLex s.toProd ≤ toLex t.toProd := h
  rw [Prod.Lex.le_iff] at h'
  rcases h' with h1 | ⟨_, h2⟩
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
        rw [isChain, List.isChain_cons] at halt; exact halt.2
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
              rw [isChain, List.isChain_cons] at halt
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

/-- **Greedy optimality for `leadingChain`.** Any `isChain` `c` drawn in order from `m`
that starts at `m`'s head is no longer than the leading chain. Hence `leadingChain m`
realizes the maximal consecutive-begin chain length from `min m` — the reusable half of
Prop 3.3 that both directions of `chainLenPreserved` need. -/
lemma leadingChain_length_ge (m : Multisegment) (c : List Segment)
    (hc : isChain c) (hsub : c <+ m.segments) (hhead : c.head? = m.segments.head?) :
    c.length ≤ (leadingChain m).val.segments.length := by
  cases c with
  | nil => simp
  | cons x c' =>
    unfold leadingChain
    split
    · rename_i hseg; rw [hseg] at hsub; exact absurd hsub (by simp)
    · rename_i first rest hseg
      rw [hseg] at hhead hsub
      simp only [List.head?_cons, Option.some.injEq] at hhead; subst hhead
      have hrest_sorted : rest.Pairwise (· ≤ ·) :=
        (List.pairwise_cons.mp (hseg ▸ m.is_sorted)).2
      have hc' : isChain c' := by rw [isChain, List.isChain_cons] at hc; exact hc.2
      have hc'sub : c' <+ rest := by
        rcases List.sublist_cons_iff.mp hsub with h | ⟨r, hr, hrs⟩
        · exact (List.sublist_cons_self x c').trans h
        · obtain ⟨_, rfl⟩ := List.cons.inj hr; exact hrs
      have hlink : ∀ h : c' ≠ [], chainLink (([x]).getLast (by simp)) (c'.head h) := by
        intro h
        cases c' with
        | nil => exact absurd rfl h
        | cons a2 c'' =>
          rw [isChain, List.isChain_cons] at hc
          simpa using hc.1 a2 (by simp)
      have key := go_optimal rest hrest_sorted [x] (by simp) c' hc' hc'sub hlink
      simpa [extendChain, Nat.add_comm] using key

/-- Membership interface for greedy optimality: a chain whose elements all lie in `m` and
whose head is `min m` is no longer than the leading chain. The sublist is recovered from
nodup + sortedness, so callers need only supply membership. -/
lemma leadingChain_length_ge' (m : Multisegment) (c : List Segment)
    (hc : isChain c) (hmem : ∀ x ∈ c, x ∈ m.segments) (hhead : c.head? = m.segments.head?) :
    c.length ≤ (leadingChain m).val.segments.length := by
  have hlt : c.Pairwise (· < ·) := by
    haveI : Trans (α := Segment) (· < ·) (· < ·) (· < ·) := ⟨lt_trans⟩
    exact (hc.imp (fun {a b} h => chainLink_imp_lt a b h)).pairwise
  have hnd : c.Nodup := hlt.imp (fun {a b} h => ne_of_lt h)
  have hsub : c <+ m.segments :=
    List.sublist_of_subperm_of_pairwise (List.subperm_of_subset hnd (fun x hx => hmem x hx))
      (isChain_imp_sorted c hc) m.is_sorted
  exact leadingChain_length_ge m c hc hsub hhead

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
lemma leadingChain_length_ge'' (m : Multisegment) (c : List Segment) (sₘ : Segment)
    (hc : isChain c) (hmem : ∀ x ∈ c, x ∈ m.segments) (hsₘ : m.segments.head? = some sₘ)
    (hbeg : ∀ x, c.head? = some x → x.a = sₘ.a) :
    c.length ≤ (leadingChain m).val.segments.length := by
  cases c with
  | nil => simp
  | cons x c' =>
    have hxa : x.a = sₘ.a := hbeg x rfl
    obtain ⟨t, ht⟩ := head?_cons_ex hsₘ
    have hsₘm : sₘ ∈ m.segments := ht ▸ List.mem_cons_self
    have hxm : x ∈ m.segments := hmem x (by simp)
    have hsxb : sₘ.b ≤ x.b := seg_b_le_of_le_of_a_eq (head_le_mem m sₘ hsₘ x hxm) hxa.symm
    have hc' : isChain c' := by rw [isChain, List.isChain_cons] at hc; exact hc.2
    have hnew : isChain (sₘ :: c') := by
      rw [isChain, List.isChain_cons]
      refine ⟨?_, hc'⟩
      intro b hb
      rw [isChain, List.isChain_cons] at hc
      have hxb : chainLink x b := hc.1 b hb
      exact ⟨⟨by have := hxb.1.1; omega, by have := hxb.1.2; omega⟩, by have := hxb.2; omega⟩
    have hmem' : ∀ y ∈ (sₘ :: c'), y ∈ m.segments := by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hmy
      · exact hsₘm
      · exact hmem y (by simp [hmy])
    have hhead' : (sₘ :: c').head? = m.segments.head? := by rw [hsₘ]; rfl
    simpa using leadingChain_length_ge' m (sₘ :: c') hnew hmem' hhead'

end MW
