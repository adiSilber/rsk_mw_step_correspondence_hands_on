import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.RSK_t
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Sort
-- import Mathlib.Data.Set.Finite


set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.hashCommand false

open scoped List

def Ladder := {ms: Multisegment // isLadder ms.segments}

def subms_ladder (l : Ladder) (ms : Multisegment) := l.val ⊆ ms
infix:90 " ⊆ " => subms_ladder

instance : forall x, Decidable (isLadder x) := by
  intro x; unfold isLadder; infer_instance

lemma isLadder_sorted (segments : List Segment) :
    isLadder segments → segments.Pairwise (· ≤ ·) := by
  simp [isLadder]
  apply List.Pairwise.imp
  rintro a b ⟨aa, bb⟩
  unfold leq
  exact Or.symm (Or.inr aa)


lemma sorted_Sublist_append (R : α → α → Prop) [hasym : Std.Antisymm R]
    (l l₀: List α) (sorted : l.Pairwise R) (a : α) :
    l₀ <+ l → a ∈ l → a ∉ l₀ → (∀ b, b ∈ l₀ → R a b) → a :: l₀ <+ l := by
  intros hsub hal hal₀ hrba
  choose l₁ l₂ hl₁₂ using List.append_of_mem hal
  have h : ∀ x ∈ l₀, x ∉ l₁ ++ [a]:= by
    intros x hxl₀
    rw [hl₁₂] at sorted
    obtain ⟨h₁,h₂,h₃⟩ := List.pairwise_append.mp sorted
    have _l₁ra : ∀ x ∈ l₁, R x a := by aesop
    --
    simp; constructor
    · intro xl₁
      rw [← hasym.antisymm a x] at hxl₀ <;> tauto
    · grind
  -- back to the main goal
  trans a :: l₂
  · apply List.Sublist.cons_cons
    apply List.Sublist.of_sublist_append_right
    · apply h
    · aesop
  · rw [hl₁₂]; aesop

lemma Pairwise_append (l : List α) (a : α) R :
  l.Pairwise R -> (forall i, i ∈ l -> R i a) -> (l ++ [a]).Pairwise R := by
  intros h1 h2
  rw [List.pairwise_append]; aesop

lemma Pairwise_ReflGen_rel_getHead (R : α → α → Prop) (l : List α) (a : α)
    (h₁ : List.Pairwise R l) (ha : a ∈ l) :
    Relation.ReflGen R (l.head <| List.ne_nil_of_mem ha) a := by
  cases l with
  | nil => simp at ha
  | cons hd tl =>
    -- l.head _ reduces to hd here
    rcases List.mem_cons.mp ha with rfl | hmem
    · exact .refl
    · exact .single ((List.pairwise_cons.mp h₁).1 a hmem)


lemma isLadder_extend l (hl : isLadder l) s₀ s₁ :
    s₀ ∈ l.head? → s₁ ≪ s₀ →
    isLadder (s₁ :: l) := by
  intro h_head h_ll
  unfold isLadder at hl ⊢
  cases l with
  | nil => simp at h_head
  | cons hd tl =>
    rw [decide_eq_true_eq] at *
    have hhd : hd = s₀ := by simpa using h_head
    refine List.Pairwise.cons ?_ hl
    -- refine List.Pairwise.cons ?_ hl
    intro y hy
    -- annotation forces (hd :: tl).head _ to reduce to hd here
    have h : Relation.ReflGen (· ≪ ·) hd y :=
      Pairwise_ReflGen_rel_getHead (· ≪ ·) _ y hl hy
    rw [hhd] at h
    cases h with
    | refl       => exact h_ll
    | single hsy => exact ll_trans _ _ _ h_ll hsy



def Ladder_extend (l : Ladder) s₀ s₁ :
    s₀ ∈ l.val.segments.head? -> s₁ ≪ s₀-> Ladder := by
  intros hs0 hs01
  let app := s₁ :: l.val.segments
  have app_isLadder : isLadder app := by
    apply isLadder_extend <;> aesop (add simp l.prop)
  exact ⟨⟨app, isLadder_sorted _ app_isLadder⟩, app_isLadder⟩

lemma Ladder_sublist_extend (ms : Multisegment)
    (l : Ladder) (h : l ⊆ ms) s₀ s₁
    (hs0 : s₀ ∈ l.val.segments.head?)
    (hs01 : s₁ ≪ s₀) :
    s₁ ∈ ms.segments → Ladder_extend l s₀ s₁ hs0 hs01 ⊆ ms := by
  intro hs1
  -- Reuse isLadder_extend to recover s₁ ≪ b for every b ∈ l.val.segments
  have hext : isLadder (s₁ :: l.val.segments) :=
    isLadder_extend l.val.segments l.prop s₀ s₁ hs0 hs01
  have h_ll : ∀ b ∈ l.val.segments, s₁ ≪ b :=
    (List.pairwise_cons.mp hext).1
  -- s₁ ≤ b follows from s₁ ≪ b by lex projection on the first component
  have h_le : ∀ b ∈ l.val.segments, s₁ ≤ b := fun b hb => by
    rcases h_ll b hb with ⟨ha, _⟩
    apply Prod.Lex.left; assumption
  -- s₁ ∉ l.val.segments, since otherwise we'd have s₁ ≪ s₁ ⇒ s₁.a < s₁.a
  have h_notin : s₁ ∉ l.val.segments := fun hc =>
    lt_irrefl _ (h_ll s₁ hc).1
  -- Now apply sorted_Sublist_append at the ≤ level
  exact sorted_Sublist_append (· ≤ ·) ms.segments l.val.segments
    ms.is_sorted s₁ h hs1 h_notin h_le
