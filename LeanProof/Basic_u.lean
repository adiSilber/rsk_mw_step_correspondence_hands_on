import Mathlib.Order.Interval.Lex
import Mathlib.Data.List.Sublists
import Mathlib.Data.Set.Lattice
import Mathlib.Data.List.Pairwise
import Mathlib.Logic.Relation
import Mathlib.Order.Interval.Basic
import Mathlib.Algebra.Order.Group.Int
import LeanProof.Basic_t
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false

open scoped List

/-! # Shared basic definitions for the RSK / Mœglin–Waldspurger development.

The `Segment` type, its accessors, and the `Multisegment` (a sorted list of
segments) are used by both `LeanProof.LadderMinimal` and
`LeanProof.MultiSegments`.
-/


-- /-- Left shift of a segment: `[a,b] ↦ [a-1,b-1]`, written as `\lshft Δ` in the paper. -/
-- def leftShift (s : Segment) : Segment :=
--   ⟨⟨s.a - 1, s.b - 1⟩, by
--     simpa [a, b, sub_eq_add_neg] using Int.add_le_add_right s.fst_le_snd (-1)⟩


instance : DecidableEq Segment := inferInstanceAs (DecidableEq (NonemptyInterval ℤ))

instance : Repr Segment where
  reprPrec s _ := reprPrec (s.a, s.b) 0

/-- The explicit description of the lexicographic order on segments. -/
lemma Segment.le_def (s₁ s₂ : Segment) :
    s₁ ≤ s₂ ↔ s₁.a < s₂.a ∨ (s₁.a = s₂.a ∧ s₁.b ≤ s₂.b) :=
  Iff.rfl

/-- Two segments agreeing on begin and end are equal. -/
private lemma Segment.ext' {s t : Segment} (ha : s.a = t.a) (hb : s.b = t.b) : s = t :=
  NonemptyInterval.ext (Prod.ext ha hb)

/-- The lexicographic order on segments is a linear order. -/
instance : LinearOrder Segment where
  le := (· ≤ ·)
  le_refl s := (Segment.le_def s s).mpr (Or.inr ⟨rfl, le_rfl⟩)
  le_trans s t u h₁ h₂ := by
    have h₁ := (Segment.le_def s t).mp h₁
    have h₂ := (Segment.le_def t u).mp h₂
    exact (Segment.le_def s u).mpr (by omega)
  le_antisymm s t h₁ h₂ := by
    have h₁ := (Segment.le_def s t).mp h₁
    have h₂ := (Segment.le_def t s).mp h₂
    exact Segment.ext' (by omega) (by omega)
  le_total s t := by
    rw [Segment.le_def, Segment.le_def]; omega
  toDecidableLE s t := inferInstanceAs (Decidable (s.a < t.a ∨ (s.a = t.a ∧ s.b ≤ t.b)))

/-- The explicit description of the strict lexicographic order on segments. -/
lemma Segment.lt_def (s t : Segment) :
    s < t ↔ s.a < t.a ∨ (s.a = t.a ∧ s.b < t.b) := by
  change (s ≤ t ∧ ¬ t ≤ s) ↔ _
  rw [Segment.le_def, Segment.le_def]; omega

/-- Every list of segments is a multisegment, `Σ Δ`: its segments in increasing order (repeats
kept). Used silently wherever a `Multisegment` is expected and a list is given. -/
instance : Coe (List Segment) Multisegment where
  coe l := ⟨l.insertionSort (· ≤ ·), List.pairwise_insertionSort _ _⟩

@[simp] lemma coe_list_segments (l : List Segment) :
    (l : Multisegment).segments = l.insertionSort (· ≤ ·) := rfl

/-- The sum `l₁ + l₂` of two lists of segments is a multisegment: their formal sum `Σ Δ`, the
multisegment of all their segments. -/
instance : HAdd (List Segment) (List Segment) Multisegment :=
  ⟨fun l₁ l₂ => ((l₁ ++ l₂ : List Segment) : Multisegment)⟩

@[simp] lemma list_add_list (l₁ l₂ : List Segment) :
    (l₁ + l₂ : Multisegment) = ((l₁ ++ l₂ : List Segment) : Multisegment) := rfl

@[trans]
lemma ll_trans x y z : x ≪ y → y ≪ z → x ≪ z := by
  simp [(· ≪ ·)]; omega

instance : Transitive (· ≪ ·) := ll_trans


instance : ∀ (ms₀ ms₁ : Multisegment), Decidable (ms₀ ⊆ ms₁) := by
  unfold subms; infer_instance

-- Concrete facts (e.g. about an example multisegment in an `_e` file) are checked by `decide`.
-- Declared first, so it is tried after the more specific rules below.
macro_rules | `(tactic| auto_prop) => `(tactic| decide)

/-! ### What `auto_prop` knows about segments (for `Segment a b`) -/

/-- Every segment satisfies `a ≤ b`; `grind` learns it whenever it meets `s.a` or `s.b`. -/
lemma Segment.a_le_b (s : Segment) : s.a ≤ s.b := s.fst_le_snd
grind_pattern Segment.a_le_b => s.a
grind_pattern Segment.a_le_b => s.b

-- `grind` may unfold `⊆` and `≪` on segments.
attribute [grind =] subsegment ll

/-! ### `maximum` of `{f x | x ∈ l}` -/

lemma maximum_mem {α} [LinearOrder α] (S : Set α) [Fintype S] (h : S.Nonempty) :
    maximum S h ∈ S := Set.mem_toFinset.mp (Finset.max'_mem _ _)

lemma le_maximum {α} [LinearOrder α] (S : Set α) [Fintype S] (h : S.Nonempty) {x : α}
    (hx : x ∈ S) : x ≤ maximum S h := Finset.le_max' _ _ (Set.mem_toFinset.mpr hx)

lemma first_mem {α} [LinearOrder α] (S : Set α) [Fintype S] (h : S.Nonempty) :
    first S h ∈ S := Set.mem_toFinset.mp (Finset.min'_mem _ _)

@[simp] lemma mem_sorted {α} [LinearOrder α] {S : Set α} [Fintype S] {x : α} :
    x ∈ sorted S ↔ x ∈ S := by
  simp [sorted]

lemma sorted_eq_nil {α} [LinearOrder α] {S : Set α} [Fintype S] (h : S = ∅) : sorted S = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr; intro x hx; simp [h] at hx

/-- `let x ∈ S; e` is `e` at any member of `S`. -/
lemma anyOf_eq {α β} [LinearOrder α] {S : Set α} [Fintype S] {f : (x : α) → x ∈ S → β}
    {h : S.Nonempty} {hf : ∀ x (hx : x ∈ S) y (hy : y ∈ S), f x hx = f y hy}
    {x : α} (hx : x ∈ S) : anyOf S f h hf = f x hx :=
  hf _ _ _ hx

/-- Finite sets with the same sorted list are equal. -/
lemma eq_of_sorted_eq {α} [LinearOrder α] {S T : Set α} [Fintype S] [Fintype T]
    (h : sorted S = sorted T) : S = T := by
  ext x
  have := congrArg (x ∈ ·) h
  simpa using this

/-- Two segments with the same begin and end are equal. -/
lemma Segment.ext_ab {s t : Segment} (ha : s.a = t.a) (hb : s.b = t.b) : s = t :=
  Segment.ext' ha hb

/-- The list comprehension `[x | x ∈ l]` is `l`. -/
@[simp] lemma comprehension_id {α} (l : List α) : List.map (fun ⟨x, _⟩ => x) l.attach = l := by
  simp

/-- The list comprehension `[f x | x ∈ l]` is `l.map f`. -/
@[simp] lemma comprehension_map {α β} (l : List α) (f : α → β) :
    List.map (fun ⟨x, _⟩ => f x) l.attach = l.map f := by
  simp

/-- `{f x | x ∈ l}` is finite: it is computed by `l.map f`. -/
instance {α β} [DecidableEq β] (l : List α) (f : α → β) : Fintype {y | ∃ x ∈ l, f x = y} :=
  Fintype.ofFinset (l.map f).toFinset (by simp)

-- From here on `maximum` is used only through the two lemmas above; keeping it opaque
-- stops the elaborator from unfolding it (and timing out) inside large terms.
set_option allowUnsafeReducibility true in
attribute [irreducible] maximum

-- Likewise `first` is used only through `first_mem`.
set_option allowUnsafeReducibility true in
attribute [irreducible] first

/-- The set of members of a list is finite: it is computed by the list itself. -/
instance {α} [DecidableEq α] (l : List α) : Fintype {x | x ∈ l} :=
  Fintype.ofFinset l.toFinset (by simp)

/-- The least element of a sorted list is its head. -/
lemma first_eq_head {α} [LinearOrder α] (l : List α) (hl : l.Pairwise (· ≤ ·)) (h : l ≠ [])
    (hS : (l : Set α).Nonempty) : first l hS = l.head h := by
  unfold first
  cases l with
  | nil => exact absurd rfl h
  | cons a t =>
    apply le_antisymm
    · exact Finset.min'_le _ _ (by rw [Set.mem_toFinset]; exact List.mem_cons_self)
    · apply Finset.le_min'
      intro y hy
      rw [Set.mem_toFinset] at hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact le_rfl
      · exact (List.pairwise_cons.mp hl).1 y hy

lemma nonempty_mem_cons {α} (a : α) (l : List α) : {x | x ∈ a :: l}.Nonempty :=
  ⟨a, List.mem_cons_self⟩

/-- The members of a nonempty list form a nonempty set. -/
lemma nonempty_mem_of_ne_nil {α} {l : List α} (h : l ≠ []) : {x | x ∈ l}.Nonempty := by
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil l h
  exact ⟨x, hx⟩

/-- A comprehension `[f x | x ∈ l]` over a nonempty list is nonempty. -/
lemma comprehension_ne_nil {α β} {l : List α} (f : {x // x ∈ l} → β) (h : l ≠ []) :
    List.map f l.attach ≠ [] := by
  simpa using h

/-- A list with a `head?` is nonempty. -/
lemma ne_nil_of_head?_eq_some {α} {l : List α} {a : α} (h : l.head? = some a) : l ≠ [] := by
  rintro rfl; simp at h

lemma nonempty_image_cons {α β} (s : α) (ss : List α) (f : α → β) :
    {y | ∃ x ∈ s :: ss, f x = y}.Nonempty := ⟨f s, s, List.mem_cons_self, rfl⟩

/-- The largest begin point of a list of segments is at most its largest end point. -/
lemma maximum_a_le_maximum_b (l : List Segment) (h₁ h₂) :
    maximum {(x.a) | x ∈ l} h₁ ≤ maximum {(x.b) | x ∈ l} h₂ := by
  obtain ⟨x, hx, hxa⟩ := maximum_mem {(x.a) | x ∈ l} h₁
  rw [← hxa]
  exact le_trans x.fst_le_snd (le_maximum _ h₂ ⟨x, hx, rfl⟩)

-- Teach `auto_prop` (the tactic that finds omitted proof arguments) the facts above.
macro_rules | `(tactic| auto_prop) => `(tactic| exact List.getElem_mem _)
macro_rules | `(tactic| auto_prop) => `(tactic| exact nonempty_mem_cons _ _)
-- (`apply …; assumption` rather than `exact … ‹_›`: a failing `‹_›` is only reported, not
-- backtracked, so it would block the other alternatives.)
macro_rules
  | `(tactic| auto_prop) =>
    `(tactic| (apply nonempty_mem_of_ne_nil; apply comprehension_ne_nil; assumption))
macro_rules | `(tactic| auto_prop) => `(tactic| (apply List.ne_nil_of_mem; assumption))
macro_rules | `(tactic| auto_prop) => `(tactic| (apply ne_nil_of_head?_eq_some; assumption))
macro_rules | `(tactic| auto_prop) => `(tactic| (apply List.ne_nil_of_length_pos; assumption))
macro_rules | `(tactic| auto_prop) => `(tactic| exact nonempty_image_cons _ _ _)
macro_rules | `(tactic| auto_prop) => `(tactic| exact maximum_a_le_maximum_b _ _ _)

-- Lets the index rule of `Fundamentals_t` unfold `Indices`.
attribute [grind =] Indices

instance (j : ℕ) (m : Multisegment) (i : List ℕ) : Decidable (i ∈ Indices j m) := by
  unfold Indices; infer_instance

/-! ### Comprehensions with a condition, and lists as multisets -/

/-- A condition binder `[f | x ∈ l, p]` lists the values at the elements of `l` satisfying `p`. -/
lemma comprehension_cond {α β} (l : List α) (p : α → Prop) [DecidablePred p]
    (f : (a : α) → a ∈ l → p a → β) :
    ∀ (L : List α) (hL : L = l.filter (fun a => decide (p a))),
    l.attach.flatMap (fun ⟨a, ha⟩ => if h : p a then [f a ha h] else [])
      = L.attach.map (fun ⟨a, ha⟩ =>
          f a ((List.mem_filter (p := fun a => decide (p a))).mp (hL ▸ ha)).1
            (of_decide_eq_true
              ((List.mem_filter (p := fun a => decide (p a))).mp (hL ▸ ha)).2)) := by
  induction l with
  | nil => intro L hL; subst hL; rfl
  | cons a l ih =>
    intro L hL
    by_cases hp : p a
    · rw [List.filter_cons_of_pos (p := fun a => decide (p a)) (decide_eq_true hp)] at hL
      subst hL
      simp only [List.attach_cons, List.flatMap_cons, List.flatMap_map, dif_pos hp,
        List.singleton_append, List.map_cons, List.map_map]
      congr 1
      exact ih (fun a ha h => f a (List.mem_cons_of_mem _ ha) h) _ rfl
    · rw [List.filter_cons_of_neg (p := fun a => decide (p a)) (by simpa using hp)] at hL
      subst hL
      simp only [List.attach_cons, List.flatMap_cons, List.flatMap_map, dif_neg hp,
        List.nil_append]
      exact ih (fun a ha h => f a (List.mem_cons_of_mem _ ha) h) _ rfl

/-- `[l[j] | j < l.length]` is `l`. -/
lemma pmap_range_getElem {α} (l : List α) :
    (List.range l.length).pmap (fun j hj => l[j]) (fun _ h => List.mem_range.mp h) = l := by
  apply List.ext_getElem <;> simp

lemma filterMap_eq_flatMap_toList {α β} (f : α → Option β) (l : List α) :
    l.filterMap f = l.flatMap (fun a => (f a).toList) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filterMap_cons, List.flatMap_cons, ih]
    rcases f a with _ | b <;> rfl

/-- Removing the elements of `c` one by one from `l` leaves `a`, when `a ++ c` lists `l`. -/
lemma perm_foldl_erase_of_perm_append {α} [DecidableEq α] : ∀ (c a l : List α),
    (a ++ c) ~ l → a ~ c.foldl List.erase l := by
  intro c
  induction c with
  | nil => intro a l h; simpa using h
  | cons x c ih =>
    intro a l h
    rw [List.foldl_cons]
    exact ih a _ (List.cons_perm_iff_perm_erase.mp (List.perm_middle.symm.trans h)).2
