import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.Ladder_t
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Sort
-- import Mathlib.Data.Set.Finite


set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.hashCommand false

open scoped List

/-- A multisegment whose segments form a ladder (pairwise `≪`). -/
def Ladder := {ms : Multisegment // isLadder ms.segments}

def subms_ladder (l : Ladder) (ms : Multisegment) := l.val ⊆ ms
infix:90 " ⊆ " => subms_ladder

instance : forall x, Decidable (isLadder x) := by
  intro x; unfold isLadder; infer_instance

lemma isLadder_sorted (segments : List Segment) :
    isLadder segments → segments.Pairwise (· ≤ ·) := by
  simp [isLadder]
  apply List.Pairwise.imp
  rintro a b ⟨aa, bb⟩
  exact (Segment.le_def a b).mpr (Or.inl aa)


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
    (List.pairwise_cons.mp (by simpa [isLadder] using hext)).1
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


/-- The list of lengths of all valid-ladder sublists of `ms` having `s` at the head. -/
def validLadderLengths (ms : Multisegment) (s : Segment) : List ℕ :=
  (ms.segments.sublists.filter (fun l => isLadder l ∧ s ∈ l.head?)).map List.length

/-- The one-segment ladder `[s]` is always valid, so the list is non-empty. -/
lemma validLadderLengths_ne_nil (ms : Multisegment) (s : Segment)
    (hs : s ∈ ms.segments) : validLadderLengths ms s ≠ [] := by
  apply List.ne_nil_of_mem (a := [s].length)
  apply List.mem_map_of_mem
  simp [hs, isLadder]

/-- The key fact: `depth_of_segment + 1` is exactly the maximum valid ladder length. -/
lemma depth_succ_eq_max (ms : Multisegment) (s : Segment) (hs : s ∈ ms.segments) :
    depth_of_segment ms s hs + 1 =
      (validLadderLengths ms s).max (validLadderLengths_ne_nil ms s hs) := by
  have h_one_in : (1 : ℕ) ∈ validLadderLengths ms s := by
    have h_s_in : [s] ∈ ms.segments.sublists.filter (fun l => isLadder l ∧ s ∈ l.head?) := by
      simp [hs, isLadder]
    have := List.mem_map_of_mem (f := List.length) h_s_in
    simpa [validLadderLengths] using this
  have h_max_ge := List.le_max_of_mem h_one_in
  have h_unfold : depth_of_segment ms s hs =
      (validLadderLengths ms s).max (validLadderLengths_ne_nil ms s hs) - 1 := by
    unfold depth_of_segment validLadderLengths; rfl
  omega

lemma depth_witness (ms : Multisegment) (s : Segment)
    (hs : s ∈ ms.segments) :
    ∃l : Ladder, l.val.segments <+ ms.segments ∧
      s ∈ l.val.segments.head? ∧
      depth_of_segment ms s hs + 1 = l.val.segments.length := by
  rw [depth_succ_eq_max ms s hs]
  obtain ⟨a, ha_mem, ha_len⟩ :=
    List.exists_of_mem_map (List.max_mem (validLadderLengths_ne_nil ms s hs))
  simp at ha_mem
  obtain ⟨h₁, h₂, h₃⟩ := ha_mem
  exact ⟨⟨⟨a, isLadder_sorted _ h₂⟩, h₂⟩, h₁, h₃, ha_len.symm⟩

lemma depth_witness' (ms : Multisegment) (s : Segment)
    (hs : s ∈ ms.segments)
    (l : Ladder) (hl : l.val.segments <+ ms.segments)
    (hls : s ∈ l.val.segments.head?) :
    depth_of_segment ms s hs + 1 ≥ l.val.segments.length := by
  rw [depth_succ_eq_max ms s hs]
  apply List.le_max_of_mem
  apply List.mem_map_of_mem
  apply List.mem_filter_of_mem
  · simpa using hl
  · aesop (add simp l.prop)

lemma ll_ne_depth (ms : Multisegment) (s₁ s₂ : Segment)
  (hs₁ : s₁ ∈ ms.segments) (hs₂ : s₂ ∈ ms.segments) :
  s₁ ≪ s₂ → depth_of_segment ms s₂ hs₂ < depth_of_segment ms s₁ hs₁ := by
intro hll
obtain ⟨L₂, hL₂_sub, hL₂_head, hL₂_len⟩ := depth_witness ms s₂ hs₂
have hbound := depth_witness' ms s₁ hs₁
  (Ladder_extend L₂ s₂ s₁ hL₂_head hll)
  (Ladder_sublist_extend ms L₂ hL₂_sub s₂ s₁ hL₂_head hll hs₁)
  rfl
have hlen : (Ladder_extend L₂ s₂ s₁ hL₂_head hll).val.segments.length =
            L₂.val.segments.length + 1 := rfl
omega

lemma segment_rel_cases (s₁ s₂ : Segment) :
    s₁ ≪ s₂  ∨  s₂ ≪ s₁  ∨  s₁ ⊆ s₂  ∨  s₂ ⊆ s₁ := by
  simp [(· ≪ ·), subsegment] at *; omega


/-- A bucket is a nested family: any two of its segments are `⊆`-comparable
(same depth rules out `≪` in either direction). -/
lemma bucket_sink (ms : Multisegment) d s₁ s₂
    (hs₁ : s₁ ∈ bucket ms d) (hs₂ : s₂ ∈ bucket ms d) :
    s₁ ⊆ s₂ ∨ s₂ ⊆ s₁ := by
  simp [bucket] at hs₁ hs₂
  obtain rl|rl|rl|rl := segment_rel_cases s₁ s₂
    <;> try tauto
  all_goals { apply ll_ne_depth ms at rl; omega }

/-- Proof-side name for the contents of `bucket` before the sort (the depth-`d` filter). -/
def bucketRaw (ms : Multisegment) (d : ℕ) : List {s : Segment // s ∈ ms.segments} :=
  ms.segments.attach.filter fun ⟨s, hs⟩ => depth_of_segment ms s hs = d

/-- The bucket is genuinely sorted by reverse inclusion: each later element is `⊆`
each earlier one.

`⊆` is not total on arbitrary segments, so `List.pairwise_insertionSort` cannot apply
directly. The trick: on the subtype `{x // x ∈ bucketRaw ms d}` the order *is* total
(`bucket_sink`), so we sort the `attach`ed list there and transport the result back
along `List.map_insertionSort`. -/
lemma bucket_pairwise (ms : Multisegment) (d : ℕ) :
    (bucket ms d).Pairwise
      (fun x y : {s : Segment // s ∈ ms.segments} => y.val ⊆ x.val) := by
  haveI : Std.Total (fun x y : {x // x ∈ bucketRaw ms d} => (y.val.val : Segment) ⊆ x.val.val) :=
    ⟨fun x y => bucket_sink ms d y.val x.val
      ((List.mem_insertionSort _).mpr y.prop) ((List.mem_insertionSort _).mpr x.prop)⟩
  haveI : IsTrans _ (fun x y : {x // x ∈ bucketRaw ms d} => (y.val.val : Segment) ⊆ x.val.val) :=
    ⟨fun x y z hxy hyz => by simp only [subsegment] at *; omega⟩
  have key : bucket ms d =
      ((bucketRaw ms d).attach.insertionSort
        (fun x y => (y.val.val : Segment) ⊆ x.val.val)).map Subtype.val := by
    rw [show bucket ms d
        = (bucketRaw ms d).insertionSort
            (fun x y : {s : Segment // s ∈ ms.segments} => y.val ⊆ x.val) from rfl,
      List.map_insertionSort _
        (fun x y : {s : Segment // s ∈ ms.segments} => y.val ⊆ x.val)
        Subtype.val ((bucketRaw ms d).attach) (fun a _ b _ => Iff.rfl),
      List.attach_map_subtype_val]
  rw [key, List.pairwise_map]
  exact List.pairwise_insertionSort _ _

/-- The bucket, projected to segments, is fully `⊇`-nested: each later element is `⊆`
each earlier one. (The admissible-enumeration nesting `Δ_{ik1} ⊇ … ⊇ Δ_{ikl}`.) -/
lemma bucket_nested (ms : Multisegment) (d : ℕ) :
    ((bucket ms d).map (·.val)).Pairwise (fun s t => subsegment t s) := by
  rw [List.pairwise_map]
  exact bucket_pairwise ms d

/-- The bucket, projected to segments, is `a`-ascending. -/
lemma bucket_sorted (ms : Multisegment) (d : ℕ) :
    ((bucket ms d).map (·.val)).Pairwise (·.a ≤ ·.a) :=
  (bucket_nested ms d).imp (fun h => h.1)

/-- Consecutive list elements form a `zip`-with-tail pair. -/
lemma mem_zip_tail_of_split {α} (l₁ : List α) (a b : α) (l₂ : List α) :
    (a, b) ∈ (l₁ ++ a :: b :: l₂).zip (l₁ ++ a :: b :: l₂).tail := by
  induction l₁ with
  | nil => simp [List.zip_cons_cons]
  | cons c cs ih =>
    rcases hX : cs ++ a :: b :: l₂ with _ | ⟨x, X⟩
    · simp at hX
    · have : (c :: cs ++ a :: b :: l₂) = c :: x :: X := by rw [List.cons_append, hX]
      rw [this, List.tail_cons, List.zip_cons_cons, List.mem_cons]; right
      have ih' := ih; rw [hX] at ih'; simpa using ih'

/-- Converse of `mem_zip_tail_of_split`: a `zip`-with-tail pair is a consecutive pair. -/
lemma zip_tail_split {α} (l : List α) (s t : α) (h : (s, t) ∈ l.zip l.tail) :
    ∃ l₁ l₂, l = l₁ ++ s :: t :: l₂ := by
  induction l with
  | nil => simp at h
  | cons a l' ih =>
    cases l' with
    | nil => simp at h
    | cons b l'' =>
      rw [List.tail_cons, List.zip_cons_cons, List.mem_cons] at h
      rcases h with heq | hmem
      · rw [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
        exact ⟨[], l'', rfl⟩
      · obtain ⟨l₁, l₂, hl⟩ := ih hmem
        exact ⟨a :: l₁, l₂, by rw [hl, List.cons_append]⟩

/-- Two segments agreeing on begin and end are equal. -/
lemma seg_ext {s t : Segment} (ha : s.a = t.a) (hb : s.b = t.b) : s = t := by
  apply NonemptyInterval.ext; apply Prod.ext ha hb

/-- Coordinatewise-smaller segments are at least as deep: if `s.a ≤ t.a` and `s.b ≤ t.b`
then `s` heads every ladder `t` heads, so `depth t ≤ depth s`. -/
lemma depth_le_of_coord_le (m : Multisegment) (s t : Segment) (hs : s ∈ m.segments)
    (ht : t ∈ m.segments) (ha : s.a ≤ t.a) (hb : s.b ≤ t.b) :
    depth_of_segment m t ht ≤ depth_of_segment m s hs := by
  obtain ⟨L, hsub, hhead, hlen⟩ := depth_witness m t ht
  obtain ⟨rest, hcons⟩ : ∃ rest, L.val.segments = t :: rest := by
    cases h : L.val.segments with
    | nil => rw [h] at hhead; simp at hhead
    | cons a tl =>
        rw [h] at hhead
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hhead
        exact ⟨tl, by rw [hhead]⟩
  have hlad_t : (t :: rest).Pairwise (· ≪ ·) := by
    have h := L.prop
    rw [hcons] at h
    simpa [isLadder] using h
  obtain ⟨ht_rest, hrest⟩ := List.pairwise_cons.mp hlad_t
  have hlad_s : isLadder (s :: rest) := by
    simp only [isLadder, decide_eq_true_eq]
    refine List.pairwise_cons.mpr ⟨fun x hx => ?_, hrest⟩
    obtain ⟨h1, h2⟩ := ht_rest x hx; exact ⟨by omega, by omega⟩
  have hrest_sub : rest <+ m.segments := (List.tail_sublist (t :: rest)).trans (hcons ▸ hsub)
  have hsnotin : s ∉ rest := by
    intro hsr; obtain ⟨h1, _⟩ := ht_rest s hsr; omega
  have hsleb : ∀ b ∈ rest, s ≤ b := by
    intro b hb'; obtain ⟨h1, _⟩ := ht_rest b hb'
    have hlt : s.a < b.a := by omega
    apply Prod.Lex.left; exact hlt
  have hsub_s : s :: rest <+ m.segments :=
    sorted_Sublist_append (· ≤ ·) m.segments rest m.is_sorted s hrest_sub hs hsnotin hsleb
  have hge := depth_witness' m s hs ⟨⟨s :: rest, isLadder_sorted _ hlad_s⟩, hlad_s⟩ hsub_s (by simp)
  rw [hcons] at hlen; simp only [List.length_cons] at hge hlen; omega

/-! ## Lemma 2.1 (Gurevich–Lapid)

The six parts of Lemma 2.1 about the depth function `depth_of_segment`. Part (1) iterates
the single-step predecessor; parts (2)–(5) relate a begin/end comparison plus a depth
comparison to containment; part (6) is the interpolation lemma. (Depth is Lean-mirrored
vs. the paper, but the statements are the faithful Lean translations.) -/

/-- Every segment at depth `d+1` has a strict predecessor at depth `d`. -/
lemma exists_pred_at_depth (m : Multisegment) (d : ℕ) (s : Segment)
    (hs : s ∈ m.segments) (hd : depth_of_segment m s hs = d + 1) :
    ∃ (s' : Segment) (hs' : s' ∈ m.segments),
      depth_of_segment m s' hs' = d ∧ s ≪ s' := by
  obtain ⟨L, hL_sub, hL_head, hL_len⟩ := depth_witness m s hs
  rw [hd] at hL_len
  match h_seg : L.val.segments with
  | [] => rw [h_seg] at hL_head; simp at hL_head
  | [_] => rw [h_seg] at hL_len; simp at hL_len
  | a :: b :: rest =>
    rw [h_seg] at hL_head; simp [List.head?] at hL_head; subst a
    have hpw : (s :: b :: rest).Pairwise (· ≪ ·) := by
      have h := L.property
      rw [h_seg] at h
      simpa [isLadder] using h
    have h_ll : s ≪ b := (List.pairwise_cons.mp hpw).1 b List.mem_cons_self
    have hb_in : b ∈ m.segments := (h_seg ▸ hL_sub).subset (by simp)
    have hpw_tail : isLadder (b :: rest) := by
      simp only [isLadder, decide_eq_true_eq]
      exact (List.pairwise_cons.mp hpw).2
    have h_ge : depth_of_segment m b hb_in + 1 ≥ (b :: rest).length :=
      depth_witness' m b hb_in ⟨⟨b :: rest, isLadder_sorted _ hpw_tail⟩, hpw_tail⟩
        ((List.tail_sublist (s :: b :: rest)).trans (h_seg ▸ hL_sub)) (by simp)
    have h_lt : depth_of_segment m b hb_in < d + 1 := hd ▸ ll_ne_depth m s b hs hb_in h_ll
    rw [h_seg] at hL_len
    simp only [List.length_cons] at hL_len h_ge
    exact ⟨b, hb_in, by omega, h_ll⟩

/-- Lemma 2.1(1): every depth `k` below `depth s` is realized by a `≪`-successor of `s`
(iterating `exists_pred_at_depth`). -/
lemma exists_lower_ll : ∀ (D : ℕ) (m : Multisegment) (s : Segment) (hs : s ∈ m.segments),
    depth_of_segment m s hs = D → ∀ k, k < D →
    ∃ (s' : Segment) (hs' : s' ∈ m.segments), depth_of_segment m s' hs' = k ∧ s ≪ s' := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
    intro m s hs hsD k hk
    obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
    obtain ⟨s', hs', hs'D, hss'⟩ := exists_pred_at_depth m D' s hs hsD
    rcases Nat.lt_or_ge k D' with hkD' | hkD'
    · obtain ⟨s'', hs'', hs''k, hs's''⟩ := ih D' (by omega) m s' hs' hs'D k hkD'
      exact ⟨s'', hs'', hs''k, ll_trans _ _ _ hss' hs's''⟩
    · have hkeq : k = D' := by omega
      subst hkeq; exact ⟨s', hs', hs'D, hss'⟩

/-- Lemma 2.1(2): `b(Δᵢ) < b(Δⱼ)` and `d(i) ≤ d(j)` imply `Δⱼ ⊆ Δᵢ`. -/
lemma depth_subset_of_a_lt (m : Multisegment) (s t : Segment) (hs : s ∈ m.segments)
    (ht : t ∈ m.segments) (hab : s.a < t.a)
    (hd : depth_of_segment m s hs ≤ depth_of_segment m t ht) : t ⊆ s := by
  refine ⟨hab.le, ?_⟩
  by_contra h; push_neg at h
  have := ll_ne_depth m s t hs ht ⟨hab, h⟩; omega

/-- Lemma 2.1(3): `b(Δᵢ) ≤ b(Δⱼ)` and `d(i) < d(j)` imply `Δⱼ ⊆ Δᵢ`. -/
lemma depth_subset_of_a_le (m : Multisegment) (s t : Segment) (hs : s ∈ m.segments)
    (ht : t ∈ m.segments) (hab : s.a ≤ t.a)
    (hd : depth_of_segment m s hs < depth_of_segment m t ht) : t ⊆ s := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · exact depth_subset_of_a_lt m s t hs ht hlt hd.le
  · refine ⟨hab, ?_⟩
    by_contra h; push_neg at h
    have := depth_le_of_coord_le m s t hs ht (le_of_eq heq) h.le; omega

/-- Lemma 2.1(4): `e(Δᵢ) < e(Δⱼ)` and `d(i) ≤ d(j)` imply `Δᵢ ⊆ Δⱼ`. -/
lemma depth_subset_of_b_lt (m : Multisegment) (s t : Segment) (hs : s ∈ m.segments)
    (ht : t ∈ m.segments) (hab : s.b < t.b)
    (hd : depth_of_segment m s hs ≤ depth_of_segment m t ht) : s ⊆ t := by
  refine ⟨?_, hab.le⟩
  by_contra h; push_neg at h
  have := ll_ne_depth m s t hs ht ⟨h, hab⟩; omega

/-- Lemma 2.1(5): `e(Δᵢ) ≤ e(Δⱼ)` and `d(i) < d(j)` imply `Δᵢ ⊆ Δⱼ`. -/
lemma depth_subset_of_b_le (m : Multisegment) (s t : Segment) (hs : s ∈ m.segments)
    (ht : t ∈ m.segments) (hab : s.b ≤ t.b)
    (hd : depth_of_segment m s hs < depth_of_segment m t ht) : s ⊆ t := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · exact depth_subset_of_b_lt m s t hs ht hlt hd.le
  · refine ⟨?_, hab⟩
    by_contra h; push_neg at h
    have := depth_le_of_coord_le m s t hs ht h.le (le_of_eq heq); omega

/-- Lemma 2.1(6): between same-depth nested `s2 ⊆ s1`, any deeper `s` with `s2 ⊆ s ⊆ s1`
can be matched at depth `depth s1` by some `s3` with `s2 ⊆ s3 ⊆ s1`. -/
lemma depth_interp (m : Multisegment) (s1 s2 : Segment) (hs1 : s1 ∈ m.segments)
    (hs2 : s2 ∈ m.segments) (hd12 : depth_of_segment m s1 hs1 = depth_of_segment m s2 hs2)
    (s : Segment) (hs : s ∈ m.segments) (h2s : s2 ⊆ s) (hss1 : s ⊆ s1)
    (hds : depth_of_segment m s1 hs1 ≤ depth_of_segment m s hs) :
    ∃ (s3 : Segment) (hs3 : s3 ∈ m.segments),
      s2 ⊆ s3 ∧ s3 ⊆ s1 ∧ depth_of_segment m s3 hs3 = depth_of_segment m s1 hs1 := by
  rcases eq_or_lt_of_le hds with heq | hlt
  · exact ⟨s, hs, h2s, hss1, heq.symm⟩
  · obtain ⟨s3, hs3, hs3d, hss3⟩ := exists_lower_ll _ m s hs rfl _ hlt
    obtain ⟨hsa, hsb⟩ := hss1
    obtain ⟨h2a, h2b⟩ := h2s
    obtain ⟨h3a, h3b⟩ := hss3
    have hs31 : s3 ⊆ s1 := depth_subset_of_a_lt m s1 s3 hs1 hs3 (by omega) (by omega)
    have h2s3 : s2 ⊆ s3 := depth_subset_of_b_lt m s2 s3 hs2 hs3 (by omega) (by omega)
    exact ⟨s3, hs3, h2s3, hs31, hs3d⟩
