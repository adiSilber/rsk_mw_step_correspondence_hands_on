import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.Ladder1_t
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite.Basic

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false

/-! `depthSet m s` is finite: it equals `depthFinset m s`, computed by checking every
`j < m.segments.length` against every index list `i₀, …, iⱼ` (`indexLists`). -/

/-- All lists of length `k` with entries `< n`. -/
private def indexLists (n : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 => (indexLists n k).flatMap fun l => (List.range n).map (· :: l)

private lemma mem_indexLists (n k : ℕ) (i : List ℕ) :
    i ∈ indexLists n k ↔ i.length = k ∧ ∀ x ∈ i, x < n := by
  induction k generalizing i with
  | zero => simp [indexLists, List.length_eq_zero_iff]; rintro rfl; simp
  | succ k ih =>
    cases i with
    | nil => simp [indexLists]
    | cons x t => simp [indexLists, ih, and_comm, and_left_comm]

/-- `∃ i : Indices j m, P i` can be decided by scanning `indexLists`. -/
private lemma exists_indices_iff {j : ℕ} {m : Multisegment} (P : Indices j m → Prop) :
    (∃ i, P i) ↔
      ∃ l ∈ indexLists m.segments.length (j + 1), ∃ h : l ∈ Indices j m, P ⟨l, h⟩ :=
  ⟨fun ⟨⟨l, h⟩, hP⟩ => ⟨l, (mem_indexLists _ _ l).mpr h, h, hP⟩,
    fun ⟨l, _, h, hP⟩ => ⟨⟨l, h⟩, hP⟩⟩

instance (m : Multisegment) (s : Segment) (j : ℕ) : Decidable (j ∈ depthSet m s) := by
  unfold depthSet
  exact decidable_of_iff _ (exists_indices_iff _).symm

/-- Along the index list of a member of `depthSet`, the `a`-values strictly increase. -/
private lemma a_lt_of_chain {m : Multisegment} {j : ℕ} (i : List ℕ) (hlen : i.length = j + 1)
    (hi : ∀ k ∈ i, k < m.segments.length)
    (hchain : ∀ r (hr : r < j),
      m.segments[i[r]]'(hi _ (List.getElem_mem _)) ≪
        m.segments[i[r + 1]]'(hi _ (List.getElem_mem _))) :
    ∀ r' (hr' : r' ≤ j) r (hr : r < r'),
      (m.segments[i[r]]'(hi _ (List.getElem_mem (by omega)))).a <
        (m.segments[i[r']]'(hi _ (List.getElem_mem (by omega)))).a := by
  intro r'
  induction r' with
  | zero => intro _ r hr; omega
  | succ r' ih =>
    intro hr' r hr
    have step := (hchain r' (by omega)).1
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with h | rfl
    · exact (ih (by omega) r h).trans step
    · exact step

/-- The `j + 1` indices of a member are distinct, so `j < m.segments.length`. -/
lemma lt_length_of_mem_depthSet {m : Multisegment} {s : Segment} {j : ℕ}
    (hj : j ∈ depthSet m s) : j < m.segments.length := by
  obtain ⟨⟨i, hlen, hi⟩, -, hchain⟩ := hj
  let f : Fin (j + 1) → Fin m.segments.length := fun r =>
    ⟨i[r.val]'(by omega), hi _ (List.getElem_mem _)⟩
  have hf : Function.Injective f := by
    intro r r' h
    have hidx : i[r.val]'(by omega) = i[r'.val]'(by omega) := congrArg Fin.val h
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · have := a_lt_of_chain i hlen hi hchain r'.val (by omega) r.val hlt
      simp only [hidx] at this; exact lt_irrefl _ this
    · have := a_lt_of_chain i hlen hi hchain r.val (by omega) r'.val hlt
      simp only [hidx] at this; exact lt_irrefl _ this
  have := Fintype.card_le_of_injective f hf
  simp at this
  omega

/-- The algorithm: every `j < m.segments.length` that passes the membership check. -/
private def depthFinset (m : Multisegment) (s : Segment) : Finset ℕ :=
  (Finset.range m.segments.length).filter (· ∈ depthSet m s)

private lemma mem_depthFinset (m : Multisegment) (s : Segment) (j : ℕ) :
    j ∈ depthFinset m s ↔ j ∈ depthSet m s := by
  simp only [depthFinset, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  exact lt_length_of_mem_depthSet

/-- The comprehension set equals the computed finite set. -/
lemma depthSet_eq_depthFinset (m : Multisegment) (s : Segment) :
    depthSet m s = ↑(depthFinset m s) := by
  ext j; simp [mem_depthFinset]

instance (m : Multisegment) (s : Segment) : Fintype (depthSet m s) :=
  Fintype.ofFinset (depthFinset m s) (mem_depthFinset m s)

lemma depthSet_finite (m : Multisegment) (s : Segment) : (depthSet m s).Finite :=
  Set.toFinite _

/-- `0 ∈ depthSet m s`: the one-index list `[idxOf s]`. -/
@[grind! .]
lemma zero_mem_depthSet {m : Multisegment} {s : Segment} (hs : s ∈ m.segments) :
    0 ∈ depthSet m s := by
  have h_lt : m.segments.idxOf s < m.segments.length := List.idxOf_lt_length_iff.mpr hs
  refine ⟨⟨[m.segments.idxOf s], by simp [Indices, h_lt]⟩, ?_,
    fun r hr => absurd hr (Nat.not_lt_zero r)⟩
  exact List.getElem_idxOf h_lt

attribute [grind ., grind →] Set.nonempty_of_mem
