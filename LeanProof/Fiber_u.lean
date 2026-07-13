import LeanProof.Fiber_t
import LeanProof.RSK_u

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false

/-- The fiber is sorted by reverse inclusion: each later element is `⊆` each earlier one.

`⊆` is not total on arbitrary segments, so `List.pairwise_insertionSort` cannot apply
directly. The trick: on the subtype `{x // x ∈ bucket ms d}` the order *is* total
(`bucket_sink`), so we sort the `attach`ed bucket there and transport the result back
along `List.map_insertionSort`. -/
lemma fiber_pairwise (ms : Multisegment) (d : ℕ) :
    (fiber ms d).Pairwise
      (fun x y : {s : Segment // s ∈ ms.segments} => y.val ⊆ x.val) := by
  haveI : Std.Total (fun x y : {x // x ∈ bucket ms d} => (y.val.val : Segment) ⊆ x.val.val) :=
    ⟨fun x y => bucket_sink ms d y.val x.val y.prop x.prop⟩
  haveI : IsTrans _ (fun x y : {x // x ∈ bucket ms d} => (y.val.val : Segment) ⊆ x.val.val) :=
    ⟨fun x y z hxy hyz => by simp only [subsegment] at *; omega⟩
  have key : fiber ms d =
      ((bucket ms d).attach.insertionSort
        (fun x y => (y.val.val : Segment) ⊆ x.val.val)).map Subtype.val := by
    unfold fiber
    rw [List.map_insertionSort _
        (fun x y : {s : Segment // s ∈ ms.segments} => y.val ⊆ x.val)
        Subtype.val ((bucket ms d).attach) (fun a _ b _ => Iff.rfl),
      List.attach_map_subtype_val]
  rw [key, List.pairwise_map]
  exact List.pairwise_insertionSort _ _

/-- The fiber, projected to segments, is fully `⊇`-nested: each later element is `⊆`
each earlier one. (The admissible-enumeration nesting `Δ_{ik1} ⊇ … ⊇ Δ_{ikl}`.) -/
lemma fiber_nested (ms : Multisegment) (d : ℕ) :
    ((fiber ms d).map (·.val)).Pairwise (fun s t => subsegment t s) := by
  rw [List.pairwise_map]
  exact fiber_pairwise ms d

/-- The fiber, projected to segments, is `a`-ascending. -/
lemma fiber_sorted (ms : Multisegment) (d : ℕ) :
    ((fiber ms d).map (·.val)).Pairwise (·.a ≤ ·.a) :=
  (fiber_nested ms d).imp (fun h => h.1)

/-- Membership in the fiber is membership in the bucket. -/
lemma mem_fiber (ms : Multisegment) (d : ℕ) (s : {s : Segment // s ∈ ms.segments}) :
    s ∈ fiber ms d ↔ s ∈ bucket ms d := by
  unfold fiber
  exact List.mem_insertionSort _
