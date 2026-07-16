import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.Ladder_t
import LeanProof.Ladder_u
import Mathlib.Data.List.Sort

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.hashCommand false

namespace RSK

/-! # RSK algorithm — single step (trusted definitions)

One step of the RSK / MW algorithm: given a multisegment `m`, produce the
maximal ladder rungs and the residual multisegment.

Each bucket's rung is the coordinatewise max of its segments (`bucketRung`);
`ladderRungs` assembles them deepest-first. The residual replaces each
consecutive nested pair `(s, t)` of a bucket by the derived segment
`[s.a, t.b]`. The correctness lemmas (`ladderRungs_isLadder`, Lemma 2.2,
Corollary 2.3) and the `Ladder`-packaged step `rskStep` live in `RSK_u`. -/

/-- The rung of bucket `d`: the largest begin point (carried by the innermost segment)
paired with the largest end point (carried by the outermost). `none` for an empty
bucket. The `by`-blocks are proofs, not computation: the two nonemptiness facts, and
well-formedness — the largest `a` belongs to some segment, whose own `b` already
bounds it from above. -/
def bucketRung (m : Multisegment) (d : ℕ) : Option Segment :=
  match (bucket m d).map (·.val) with
  | []      => none
  | s :: ss =>
    some ⟨⟨((s :: ss).map (·.a)).max (by simp), ((s :: ss).map (·.b)).max (by simp)⟩, by
      obtain ⟨x, hxmem, hxa⟩ :=
        List.exists_of_mem_map (List.max_mem (by simp : (s :: ss).map (·.a) ≠ []))
      have hxb : x.b ≤ ((s :: ss).map (·.b)).max (by simp) :=
        List.le_max_of_mem (List.mem_map_of_mem hxmem)
      have hab : x.a ≤ x.b := x.fst_le_snd
      omega⟩

/-- Maximum depth over all segments of `m`. `0` for an empty multisegment. -/
def maxDepth (m : Multisegment) : ℕ :=
  (m.segments.attach.map (fun ⟨s, hs⟩ => depth_of_segment m s hs)).foldl max 0

/-- All ladder rungs from bucket `maxDepth` down to bucket `0`. -/
def ladderRungs (m : Multisegment) : List Segment :=
  (List.range (maxDepth m + 1)).reverse.filterMap (fun k => bucketRung m k)

/-- Residual of bucket `d`: the sliding-window pairs `(sₖ, sₖ₊₁)` of the bucket
(already sorted outermost-first), each replaced by the derived segment `[sₖ.a, sₖ₊₁.b]`.
The pairs are `attach`ed so the well-formedness proof can use where they came from:
consecutive bucket elements are nested (`bucket_nested`), so `s.a ≤ t.a ≤ t.b`. -/
def bucketResidual (m : Multisegment) (d : ℕ) : List Segment :=
  let segs := (bucket m d).map (·.val)
  (segs.zip segs.tail).attach.map fun ⟨(s, t), hmem⟩ =>
    ⟨⟨s.a, t.b⟩, by
      obtain ⟨l₁, l₂, hsplit⟩ := zip_tail_split segs s t hmem
      have hnested : segs.Pairwise (fun s t => subsegment t s) := bucket_nested m d
      rw [hsplit] at hnested
      have hts : subsegment t s :=
        (List.pairwise_cons.mp (List.pairwise_append.mp hnested).2.1).1 t (by simp)
      have htab : t.a ≤ t.b := t.fst_le_snd
      obtain ⟨h1, h2⟩ := hts
      omega⟩

-- /-- `i^\vee`: the nesting successor of `s` in bucket `d` (the next, more-inner segment in
-- admissible order); `none` if `s` is the innermost element. -/
-- def bucketSucc (m : Multisegment) (d : ℕ) (s : Segment) : Option Segment :=
--   let l := (bucket m d).map (·.val)
--   ((l.zip l.tail).find? (fun p => decide (p.1 = s))).map (·.2)

/-- The changed (residual) multisegment: every bucket's residual, re-sorted. -/
def residual (m : Multisegment) : Multisegment :=
  let raw := (List.range (maxDepth m + 1)).flatMap (fun d => bucketResidual m d)
  ⟨raw.insertionSort (· ≤ ·), List.pairwise_insertionSort _ _⟩

end RSK
