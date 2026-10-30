import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.Ladder1_t
import LeanProof.Ladder1_u
import LeanProof.Ladder2_t
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.GetD
-- import Mathlib.Data.Set.Finite


set_option linter.style.setOption false
set_option autoProp.rule false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.hashCommand false

open scoped List

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
      rw [← hasym.antisymm a x (hrba x hxl₀) (_l₁ra x xl₁)] at hxl₀; tauto
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
    intro y hy
    -- annotation forces (hd :: tl).head _ to reduce to hd here
    have h : Relation.ReflGen (· ≪ ·) hd y :=
      Pairwise_ReflGen_rel_getHead (· ≪ ·) _ y hl hy
    rw [hhd] at h
    cases h with
    | refl       => exact h_ll
    | single hsy => exact ll_trans _ _ _ h_ll hsy

/-- Prepend `s₁` to the ladder `l` given a link into its head: the proof-carrying
packaging of list `cons` for ladders. -/
private def Ladder_extend (l : Ladder) s₀ s₁ :
    s₀ ∈ l.val.segments.head? -> s₁ ≪ s₀-> Ladder := by
  intros hs0 hs01
  let app := s₁ :: l.val.segments
  have app_isLadder : isLadder app := by
    apply isLadder_extend <;> aesop (add simp l.prop)
  exact ⟨⟨app, isLadder_sorted _ app_isLadder⟩, app_isLadder⟩

lemma Ladder_sublist_extend (ms : Multisegment)
    (l : Ladder) (h : l.val ⊆ ms) s₀ s₁
    (hs0 : s₀ ∈ l.val.segments.head?)
    (hs01 : s₁ ≪ s₀) :
    s₁ ∈ ms.segments → (Ladder_extend l s₀ s₁ hs0 hs01).val ⊆ ms := by
  intro hs1
  -- Reuse isLadder_extend to recover s₁ ≪ b for every b ∈ l.val.segments
  have hext : isLadder (s₁ :: l.val.segments) :=
    isLadder_extend l.val.segments l.prop s₀ s₁ hs0 hs01
  have h_ll : ∀ b ∈ l.val.segments, s₁ ≪ b :=
    (List.pairwise_cons.mp (by simpa [isLadder] using hext)).1
  -- s₁ ≤ b follows from s₁ ≪ b by lex projection on the first component
  have h_le : ∀ b ∈ l.val.segments, s₁ ≤ b := fun b hb => by
    rcases h_ll b hb with ⟨ha, _⟩
    exact (Segment.le_def _ _).mpr (Or.inl ha)
  -- s₁ ∉ l.val.segments, since otherwise we'd have s₁ ≪ s₁ ⇒ s₁.a < s₁.a
  have h_notin : s₁ ∉ l.val.segments := fun hc =>
    lt_irrefl _ (h_ll s₁ hc).1
  -- Now apply sorted_Sublist_append at the ≤ level
  exact sorted_Sublist_append (· ≤ ·) ms.segments l.val.segments
    ms.is_sorted s₁ h hs1 h_notin h_le


/-- The depth is attained: it is an element of `depthSet`. -/
lemma depth_of_segment_mem (m : Multisegment) (s : Segment) (hs : s ∈ m.segments) :
    depth_of_segment m s hs ∈ depthSet m s := by
  unfold depth_of_segment
  exact maximum_mem _ _

/-- The depth bounds every element of `depthSet`. -/
lemma le_depth_of_segment {m : Multisegment} {s : Segment} (hs : s ∈ m.segments) {j : ℕ}
    (hj : j ∈ depthSet m s) : j ≤ depth_of_segment m s hs := by
  unfold depth_of_segment
  exact le_maximum _ _ hj

/-- Along the index list of a member of `depthSet`, segments are pairwise `≪`. -/
private lemma ll_of_chain {m : Multisegment} {j : ℕ} (i : List ℕ) (hlen : i.length = j + 1)
    (hi : ∀ k ∈ i, k < m.segments.length)
    (hchain : ∀ r (hr : r < j),
      m.segments[i[r]]'(hi _ (List.getElem_mem _)) ≪
        m.segments[i[r + 1]]'(hi _ (List.getElem_mem _))) :
    ∀ r' (hr' : r' ≤ j) r (hr : r < r'),
      m.segments[i[r]]'(hi _ (List.getElem_mem (by omega))) ≪
        m.segments[i[r']]'(hi _ (List.getElem_mem (by omega))) := by
  intro r'
  induction r' with
  | zero => intro _ r hr; omega
  | succ r' ih =>
    intro hr' r hr
    have step := hchain r' (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with h | rfl
    · exact ll_trans _ _ _ (ih (by omega) r h) step
    · exact step

/-- A member `j` of `depthSet m s` gives a ladder sublist of `m`, headed by `s`, of
length `j + 1`. -/
lemma exists_ladder_of_mem_depthSet {m : Multisegment} {s : Segment} {j : ℕ}
    (hj : j ∈ depthSet m s) :
    ∃ l : List Segment, l <+ m.segments ∧ s ∈ l.head? ∧ isLadder l ∧ l.length = j + 1 := by
  obtain ⟨⟨i, hlen, _, hi⟩, h0, hchain⟩ := hj
  let l := List.ofFn fun r : Fin (j + 1) =>
    m.segments[i[r.val]'(by omega)]'(hi _ (List.getElem_mem _))
  have hpw : l.Pairwise (· ≪ ·) := by
    rw [List.pairwise_iff_getElem]
    intro r r' hr hr' hlt
    simp only [l, List.getElem_ofFn]
    simp only [l, List.length_ofFn] at hr'
    exact ll_of_chain i hlen hi hchain r' (by omega) r hlt
  have hnodup : l.Nodup := hpw.imp fun h heq => by subst heq; exact lt_irrefl _ h.1
  have hsubset : List.Subset l m.segments := by
    intro x hx
    obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hx
    exact List.getElem_mem _
  have hlad : isLadder l := by simpa [isLadder] using hpw
  refine ⟨l, List.sublist_of_subperm_of_pairwise (hnodup.subperm hsubset)
    (isLadder_sorted _ hlad) m.is_sorted, ?_, hlad, by simp [l]⟩
  simp [l, List.ofFn_succ, h0]

/-- Conversely, a ladder sublist of `m` headed by `s` gives the member
`l.length - 1` of `depthSet m s` (indices `idxOf` of its segments). -/
lemma mem_depthSet_of_ladder {m : Multisegment} {s : Segment} (l : List Segment)
    (hsub : l <+ m.segments) (hhead : s ∈ l.head?) (hl : isLadder l) :
    l.length - 1 ∈ depthSet m s := by
  have hne : l ≠ [] := by rintro rfl; simp at hhead
  have hpos : 0 < l.length := List.length_pos_iff.mpr hne
  have hmem : ∀ x ∈ l, x ∈ m.segments := fun x hx => hsub.subset hx
  have hpw : l.Pairwise (· ≪ ·) := by simpa [isLadder] using hl
  have hnodup : l.Nodup := hpw.imp fun h heq => by subst heq; exact lt_irrefl _ h.1
  refine ⟨⟨l.map m.segments.idxOf, by simp; omega, ?_, ?_⟩, ?_, ?_⟩
  · exact hnodup.map_on fun x hx y _ h => (List.idxOf_inj (hmem x hx)).mp h
  · intro k hk
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk
    exact List.idxOf_lt_length_iff.mpr (hmem x hx)
  · have h0 : l[0] = s := by
      cases l with
      | nil => exact absurd rfl hne
      | cons a t => simpa using hhead
    simp only [List.getElem_map]
    rw [List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (hmem _ (List.getElem_mem _)))]
    exact h0
  · intro r hr
    simp only [List.getElem_map]
    rw [List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (hmem _ (List.getElem_mem _))),
      List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (hmem _ (List.getElem_mem _)))]
    exact List.pairwise_iff_getElem.mp hpw r (r + 1) (by omega) (by omega) (by omega)

lemma depth_witness (ms : Multisegment) (s : Segment)
    (hs : s ∈ ms.segments) :
    ∃l : Ladder, l.val.segments <+ ms.segments ∧
      s ∈ l.val.segments.head? ∧
      depth_of_segment ms s hs + 1 = l.val.segments.length := by
  obtain ⟨l, hsub, hhead, hlad, hlen⟩ :=
    exists_ladder_of_mem_depthSet (depth_of_segment_mem ms s hs)
  exact ⟨⟨⟨l, isLadder_sorted _ hlad⟩, hlad⟩, hsub, hhead, hlen.symm⟩

lemma depth_witness' (ms : Multisegment) (s : Segment)
    (hs : s ∈ ms.segments)
    (l : Ladder) (hl : l.val.segments <+ ms.segments)
    (hls : s ∈ l.val.segments.head?) :
    depth_of_segment ms s hs + 1 ≥ l.val.segments.length := by
  have := le_depth_of_segment hs (mem_depthSet_of_ladder _ hl hls l.prop)
  omega

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

namespace Proof

/-- Proof-side: the bucket sorted outermost-first by nesting (`y ⊆ x` ⇒ `x` before `y`).
Lives in `Proof`, the namespace for public definitions of `_u` files: it is never opened, so
this list can only be meant by its full name `Proof.sortedBucket`, and no `_t` file names it.
`RSK1_u` shows it lists the fiber in the order of any admissible enumeration (`fiber_eq`). -/
def sortedBucket (ms : Multisegment) (d : ℕ) : List {s : Segment // s ∈ ms.segments} :=
  (bucket ms d).insertionSort (fun x y => y.val ⊆ x.val)

end Proof

@[simp] lemma mem_sortedBucket {ms : Multisegment} {d : ℕ} {x : {s : Segment // s ∈ ms.segments}} :
    x ∈ Proof.sortedBucket ms d ↔ x ∈ bucket ms d := List.mem_insertionSort _

lemma sortedBucket_perm (ms : Multisegment) (d : ℕ) : Proof.sortedBucket ms d ~ bucket ms d :=
  List.perm_insertionSort _ _

/-- Proof-side name for the contents of `bucket` (the depth-`d` filter). -/
private abbrev bucketRaw (ms : Multisegment) (d : ℕ) : List {s : Segment // s ∈ ms.segments} :=
  bucket ms d

/-- The bucket is genuinely sorted by reverse inclusion: each later element is `⊆`
each earlier one.

`⊆` is not total on arbitrary segments, so `List.pairwise_insertionSort` cannot apply
directly. The trick: on the subtype `{x // x ∈ bucketRaw ms d}` the order *is* total
(`bucket_sink`), so we sort the `attach`ed list there and transport the result back
along `List.map_insertionSort`. -/
lemma bucket_pairwise (ms : Multisegment) (d : ℕ) :
    (Proof.sortedBucket ms d).Pairwise
      (fun x y : {s : Segment // s ∈ ms.segments} => y.val ⊆ x.val) := by
  haveI : Std.Total (fun x y : {x // x ∈ bucketRaw ms d} => (y.val.val : Segment) ⊆ x.val.val) :=
    ⟨fun x y => bucket_sink ms d y.val x.val
      y.prop x.prop⟩
  haveI : IsTrans _ (fun x y : {x // x ∈ bucketRaw ms d} => (y.val.val : Segment) ⊆ x.val.val) :=
    ⟨fun x y z hxy hyz => by simp only [subsegment] at *; omega⟩
  have key : Proof.sortedBucket ms d =
      ((bucketRaw ms d).attach.insertionSort
        (fun x y => (y.val.val : Segment) ⊆ x.val.val)).map Subtype.val := by
    rw [show Proof.sortedBucket ms d
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
    ((Proof.sortedBucket ms d).map (·.val)).Pairwise (fun s t => subsegment t s) := by
  rw [List.pairwise_map]
  exact bucket_pairwise ms d

/-- The bucket, projected to segments, is `a`-ascending. -/
lemma bucket_sorted (ms : Multisegment) (d : ℕ) :
    ((Proof.sortedBucket ms d).map (·.val)).Pairwise (·.a ≤ ·.a) :=
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
    exact (Segment.le_def _ _).mpr (Or.inl hlt)
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

/-! ## Admissible enumerations: decidable and finite

An admissible enumeration of `𝔡⁻¹(k)` is a permutation of the list of indices of depth `k`
(`fiberIdx`), so the set of them is computed by filtering those permutations. -/

/-- Membership in `admissibleEnumerations`, with `l` determined by the length of `i`. -/
lemma mem_admissibleEnumerations_iff {m : Multisegment} {k : ℕ} {i : List ℕ} :
    i ∈ admissibleEnumerations m k ↔
      ∃ h : i ∈ Indices i.length m,
        (∀ n : Fin m.segments.length,
          (↑n ∈ i ↔ depth_of_segment m m.segments[n] (List.getElem_mem _) = k)) ∧
        (∀ r (hr : r < i.length - 1), m.segments[i[r + 1]] ⊆ m.segments[i[r]]) := by
  constructor
  · rintro ⟨⟨l, hl⟩, h1, h2⟩
    have hl' : l = i.length := hl.1.symm
    subst hl'
    exact ⟨hl, h1, fun r hr => h2 r (by change r + 1 < i.length; omega)⟩
  · rintro ⟨h, h1, h2⟩
    exact ⟨⟨i.length, h⟩, h1, fun r hr => h2 r (by change r + 1 < i.length at hr; omega)⟩

/-- Membership in `admissibleEnumerations` is decided by `mem_admissibleEnumerations_iff`. -/
instance (m : Multisegment) (k : ℕ) (i : List ℕ) : Decidable (i ∈ admissibleEnumerations m k) :=
  decidable_of_iff _ mem_admissibleEnumerations_iff.symm

/-- The indices of depth `k`, in increasing order. -/
private def fiberIdx (m : Multisegment) (k : ℕ) : List ℕ :=
  ((List.finRange m.segments.length).filter
    (fun j : Fin m.segments.length =>
      depth_of_segment m m.segments[j] (List.getElem_mem _) = k)).map Fin.val

private lemma mem_fiberIdx {m : Multisegment} {k n : ℕ} :
    n ∈ fiberIdx m k ↔
      ∃ j : Fin m.segments.length,
        depth_of_segment m m.segments[j] (List.getElem_mem _) = k ∧ j.val = n := by
  simp [fiberIdx]

private lemma nodup_fiberIdx (m : Multisegment) (k : ℕ) : (fiberIdx m k).Nodup :=
  ((List.nodup_finRange _).filter _).map Fin.val_injective

/-- An admissible enumeration is a permutation of the indices of depth `k`. -/
lemma perm_fiberIdx_of_mem {m : Multisegment} {k : ℕ} {i : List ℕ}
    (h : i ∈ admissibleEnumerations m k) : i ~ fiberIdx m k := by
  obtain ⟨⟨l, hlen, hnd, hlt⟩, h1, -⟩ := h
  refine (List.perm_ext_iff_of_nodup hnd (nodup_fiberIdx m k)).mpr fun n => ?_
  rw [mem_fiberIdx]
  constructor
  · intro hn
    exact ⟨⟨n, hlt n hn⟩, (h1 ⟨n, hlt n hn⟩).mp hn, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact (h1 j).mpr hj

/-- `admissibleEnumerations m k` is finite: the admissible permutations of `fiberIdx m k`. -/
-- A `Fintype` instance, not a `Decidable` one: it carries a computed list. Allowed in a `_u`
-- file because any two such instances agree, but it may be a little dangerous — to be checked
-- (see TODO.md).
instance (m : Multisegment) (k : ℕ) : Fintype (admissibleEnumerations m k) :=
  Fintype.ofFinset
    (((fiberIdx m k).permutations.filter
      (fun i => decide (i ∈ admissibleEnumerations m k))).toFinset)
    (fun i => by
      simp only [List.mem_toFinset, List.mem_filter, List.mem_permutations, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨perm_fiberIdx_of_mem h, h⟩⟩)

private lemma attach_eq_map_finRange {α} (l : List α) :
    l.attach = (List.finRange l.length).map
      (fun j : Fin l.length => (⟨l[j], List.getElem_mem _⟩ : {x // x ∈ l})) := by
  apply List.ext_getElem <;> simp

/-- Proof-side `Δᵢ`: the `i`-th segment of `m`, with a junk value for an invalid `i`. -/
private def Multisegment.Δ (m : Multisegment) (i : ℕ) : Segment :=
  m.segments.getD i ⟨⟨0, 0⟩, le_rfl⟩

/-- The segments of depth `k`, in index order, are the bucket. -/
private lemma fiberIdx_map_Δ (m : Multisegment) (k : ℕ) :
    (fiberIdx m k).map m.Δ = (bucket m k).map (·.val) := by
  unfold fiberIdx bucket
  rw [attach_eq_map_finRange, List.filter_map, List.map_map, List.map_map]
  apply List.map_congr_left
  intro j _
  simp [Multisegment.Δ]

private lemma Δ_eq {m : Multisegment} {n : ℕ} (h : n < m.segments.length) :
    m.Δ n = m.segments[n] := by
  simp [Multisegment.Δ, h]

private lemma perm_bucket_of_mem_Δ {m : Multisegment} {k : ℕ} {i : List ℕ}
    (h : i ∈ admissibleEnumerations m k) : i.map m.Δ ~ (bucket m k).map (·.val) := by
  rw [← fiberIdx_map_Δ]; exact (perm_fiberIdx_of_mem h).map _

private lemma pairwise_of_mem_Δ {m : Multisegment} {k : ℕ} {i : List ℕ}
    (h : i ∈ admissibleEnumerations m k) : (i.map m.Δ).Pairwise (fun s t => subsegment t s) := by
  obtain ⟨⟨l, hlen, _, hlt⟩, _, hchain⟩ := h
  haveI : IsTrans Segment (fun s t => subsegment t s) :=
    ⟨fun _ _ _ h₁ h₂ => by simp only [subsegment] at *; omega⟩
  apply List.IsChain.pairwise
  rw [List.isChain_iff_getElem]
  intro r hr
  simp only [List.length_map] at hr
  simp only [List.getElem_map]
  rw [Δ_eq (hlt _ (List.getElem_mem _)), Δ_eq (hlt _ (List.getElem_mem _))]
  have hm := List.length_map (f := m.Δ) (as := i)
  exact hchain r (by change r + 1 < l; omega)

/-- The indices of an admissible enumeration are valid indices of `m`. -/
lemma lt_length_of_mem_admissibleEnumerations {m : Multisegment} {k : ℕ} {i : List ℕ}
    (h : i ∈ admissibleEnumerations m k) : ∀ j ∈ i, j < m.segments.length := by
  obtain ⟨⟨l, _, _, hlt⟩, _⟩ := h
  exact hlt

private lemma pmap_eq_map_Δ {m : Multisegment} {i : List ℕ}
    (hlt : ∀ j ∈ i, j < m.segments.length) :
    i.pmap (fun j hj => m.segments[j]) hlt = i.map m.Δ := by
  apply List.ext_getElem
  · simp
  · intro n h₁ h₂
    simp [Δ_eq (hlt _ (List.getElem_mem (by simpa using h₁)))]

/-- An admissible enumeration lists the segments of the bucket (as a multiset). -/
lemma perm_bucket_of_mem {m : Multisegment} {k : ℕ} {i : List ℕ}
    (h : i ∈ admissibleEnumerations m k) (hlt : ∀ j ∈ i, j < m.segments.length) :
    i.pmap (fun j hj => m.segments[j]) hlt ~ (bucket m k).map (·.val) := by
  rw [pmap_eq_map_Δ]; exact perm_bucket_of_mem_Δ h

/-- An admissible enumeration lists its segments outermost-first. -/
lemma pairwise_of_mem {m : Multisegment} {k : ℕ} {i : List ℕ}
    (h : i ∈ admissibleEnumerations m k) (hlt : ∀ j ∈ i, j < m.segments.length) :
    (i.pmap (fun j hj => m.segments[j]) hlt).Pairwise (fun s t => subsegment t s) := by
  rw [pmap_eq_map_Δ]; exact pairwise_of_mem_Δ h

/-- If no segment has depth `k`, the only admissible enumeration of `𝔡⁻¹(k) = ∅` is `[]`. -/
lemma eq_nil_of_mem_admissibleEnumerations {m : Multisegment} {k : ℕ} {i : List ℕ}
    (h : ∀ j : Fin m.segments.length, depth_of_segment m m.segments[j] (List.getElem_mem _) ≠ k)
    (hi : i ∈ admissibleEnumerations m k) : i = [] := by
  obtain ⟨⟨l, -, -, hlt⟩, h1, -⟩ := hi
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro j hj
  exact h ⟨j, hlt _ hj⟩ ((h1 ⟨j, hlt _ hj⟩).mp hj)

private lemma nil_mem_admissibleEnumerations {m : Multisegment} {k : ℕ}
    (h : ∀ j : Fin m.segments.length, depth_of_segment m m.segments[j] (List.getElem_mem _) ≠ k) :
    [] ∈ admissibleEnumerations m k :=
  ⟨⟨0, by simp [Indices]⟩, fun n => by simpa using h n, fun r hr => absurd hr (by simp)⟩

/-- If some segment has depth `k`, an admissible enumeration of `𝔡⁻¹(k)` exists: the
indices of depth `k` sorted by nesting. -/
private lemma admissibleEnumerations_nonempty_of_exists {m : Multisegment} {k : ℕ}
    (h : ∃ j : Fin m.segments.length, depth_of_segment m m.segments[j] (List.getElem_mem _) = k) :
    (admissibleEnumerations m k).Nonempty := by
  -- the depth-`k` indices are pairwise `⊆`-comparable
  have hcmp : ∀ x ∈ fiberIdx m k, ∀ y ∈ fiberIdx m k,
      subsegment (m.Δ x) (m.Δ y) ∨ subsegment (m.Δ y) (m.Δ x) := by
    intro x hx y hy
    obtain ⟨jx, hjx, rfl⟩ := mem_fiberIdx.mp hx
    obtain ⟨jy, hjy, rfl⟩ := mem_fiberIdx.mp hy
    rw [Δ_eq jx.2, Δ_eq jy.2]
    exact bucket_sink m k ⟨m.segments[jx], List.getElem_mem _⟩ ⟨m.segments[jy], List.getElem_mem _⟩
      (by simp [bucket]; exact hjx) (by simp [bucket]; exact hjy)
  -- so sorting them by nesting gives an admissible enumeration
  let R : ℕ → ℕ → Prop := fun x y => subsegment (m.Δ y) (m.Δ x)
  let e := (fiberIdx m k).insertionSort R
  haveI : Std.Total (fun x y : {x // x ∈ fiberIdx m k} => R x.val y.val) :=
    ⟨fun x y => (hcmp y.val y.prop x.val x.prop)⟩
  haveI : IsTrans _ (fun x y : {x // x ∈ fiberIdx m k} => R x.val y.val) :=
    ⟨fun _ _ _ h₁ h₂ => by simp only [R, subsegment] at *; omega⟩
  have hsorted : e.Pairwise R := by
    have key : e = ((fiberIdx m k).attach.insertionSort
        (fun x y : {x // x ∈ fiberIdx m k} => R x.val y.val)).map Subtype.val := by
      rw [List.map_insertionSort _ R Subtype.val _ (fun _ _ _ _ => Iff.rfl),
        List.attach_map_subtype_val]
    rw [key, List.pairwise_map]
    exact List.pairwise_insertionSort _ _
  have hperm : e ~ fiberIdx m k := List.perm_insertionSort _ _
  have hlt : ∀ n ∈ e, n < m.segments.length := fun n hn => by
    obtain ⟨j, -, rfl⟩ := mem_fiberIdx.mp (hperm.subset hn); exact j.2
  refine ⟨e, mem_admissibleEnumerations_iff.mpr
    ⟨⟨rfl, hperm.nodup_iff.mpr (nodup_fiberIdx m k), hlt⟩, ?_, ?_⟩⟩
  · intro n
    rw [hperm.mem_iff, mem_fiberIdx]
    exact ⟨fun ⟨j', hj', hj'n⟩ => by rw [← Fin.ext hj'n]; exact hj',
      fun hn => ⟨n, hn, rfl⟩⟩
  · intro r hr
    have := List.pairwise_iff_getElem.mp hsorted r (r + 1) (by omega) (by omega) (by omega)
    simp only [R] at this
    rwa [Δ_eq (hlt _ (List.getElem_mem _)), Δ_eq (hlt _ (List.getElem_mem _))] at this

/-- Every fiber has an admissible enumeration (`[]` for an empty fiber). -/
lemma admissibleEnumerations_nonempty (m : Multisegment) (k : ℕ) :
    (admissibleEnumerations m k).Nonempty := by
  by_cases h : ∃ j : Fin m.segments.length,
    depth_of_segment m m.segments[j] (List.getElem_mem _) = k
  · exact admissibleEnumerations_nonempty_of_exists h
  · push_neg at h
    exact ⟨[], nil_mem_admissibleEnumerations h⟩

-- `first (admissibleEnumerations m k)` needs the set nonempty: `auto_prop` learns it.
attribute [grind .] admissibleEnumerations_nonempty

/-! ## The segments listed by an admissible enumeration do not depend on it -/

lemma lt_length_of_mem_of_mem_admissibleEnumerations {m : Multisegment} {k : ℕ} {i : List ℕ}
    {j : ℕ} (hj : j ∈ i) (h : i ∈ admissibleEnumerations m k) : j < m.segments.length :=
  lt_length_of_mem_admissibleEnumerations h j hj

-- The index rule learns it: `m.segments[j]` is valid for `j ∈ i`, `i ∈ admissibleEnumerations m k`.
attribute [grind →] lt_length_of_mem_of_mem_admissibleEnumerations

/-- An admissible enumeration lists the bucket sorted outermost-first. -/
lemma pmap_eq_sortedBucket {m : Multisegment} {k : ℕ} {i : List ℕ}
    (he : i ∈ admissibleEnumerations m k) (hlt : ∀ j ∈ i, j < m.segments.length) :
    i.pmap (fun j hj => m.segments[j]) hlt = (Proof.sortedBucket m k).map (·.val) := by
  by_cases h : ∃ j : Fin m.segments.length,
    depth_of_segment m m.segments[j] (List.getElem_mem _) = k
  · refine List.Perm.eq_of_pairwise (le := fun s t => subsegment t s) ?_ ?_ ?_ ?_
    · intro a b _ _ h₁ h₂
      exact seg_ext (by simp only [subsegment] at *; omega) (by simp only [subsegment] at *; omega)
    · exact pairwise_of_mem he _
    · exact bucket_nested m k
    · exact (perm_bucket_of_mem he _).trans ((sortedBucket_perm m k).map _).symm
  · push_neg at h
    have hnil : (Proof.sortedBucket m k).map (·.val) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro s hs
      obtain ⟨⟨s, hsm⟩, hsb, rfl⟩ := List.mem_map.mp hs
      rw [mem_sortedBucket] at hsb
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hsm
      exact h ⟨j, by omega⟩ (by simpa [bucket] using hsb)
    rw [hnil]
    simp [eq_nil_of_mem_admissibleEnumerations h he]

/-- Any two admissible enumerations list the same segments: this is what makes
`let i ∈ admissibleEnumerations m k; [m.segments[j] | j ∈ i]` well defined. -/
lemma segments_indep (m : Multisegment) (k : ℕ) :
    ∀ x (hx : x ∈ admissibleEnumerations m k) y (hy : y ∈ admissibleEnumerations m k),
      [m.segments[j] | j ∈ x] = [m.segments[j] | j ∈ y] := by
  intro x hx y hy
  have h1 := pmap_eq_sortedBucket hx (fun _ hj => lt_length_of_mem_admissibleEnumerations hx _ hj)
  have h2 := pmap_eq_sortedBucket hy (fun _ hj => lt_length_of_mem_admissibleEnumerations hy _ hj)
  rw [List.pmap_eq_map_attach] at h1 h2
  exact h1.trans h2.symm

attribute [grind →] segments_indep
