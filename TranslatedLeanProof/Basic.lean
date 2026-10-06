import Mathlib.Data.Set.Basic

/-! Translation of `RSK040521.tex`, §2.1, following `TRANSLATION_RULES.md`. -/

/-! ## Tex line 1 (`RSK040521.tex:297-301`)

"A segment Δ (of length b−a+1) is a subset of ℤ of the form
[a,b] = {n ∈ ℤ : a ≤ n ≤ b} for some integers a ≤ b."

Identification:
- kind: `structure` (segment: a new kind of object); `def` for `[a,b]` and the length
- introduced before: ℤ, ≤, set-builder, `+`, `−`, 1 (all standard)
- new: `[a,b]` (any integers a, b ↦ subset of ℤ); segment; length (segment ↦ integer) -/

/-- [a,b] = {n ∈ ℤ : a ≤ n ≤ b} -/
def interval (a b : ℤ) : Set ℤ := {n : ℤ | a ≤ n ∧ n ≤ b}

notation "[" a ", " b "]" => interval a b

/-- A segment Δ is a subset of ℤ of the form [a,b] for some integers a ≤ b. -/
structure Segment where
  a : ℤ
  b : ℤ
  a_le_b : a ≤ b

/-- A segment is a subset of ℤ: Δ = [a,b]. -/
instance : Coe Segment (Set ℤ) := ⟨fun Δ => [Δ.a, Δ.b]⟩

/-- The length of Δ is b − a + 1. -/
def Segment.length (Δ : Segment) : ℤ := Δ.b - Δ.a + 1

/-! ## Tex line 2 (`RSK040521.tex:303`)

"We also write ⁻Δ = [a+1,b]. Note that if a = b, then ⁻Δ is the empty set."

Identification:
- kind: `def` (built from an existing segment)
- introduced before: Δ, its a and b (implicit: Δ = [a,b]), `[·,·]` (line 1), `+`, 1, ∅
- new: `⁻` (prefix; segment ↦ subset of ℤ) -/

/-- ⁻Δ = [a+1,b] -/
def Segment.minus (Δ : Segment) : Set ℤ := [Δ.a + 1, Δ.b]

prefix:max "⁻" => Segment.minus

/-- If a = b, then ⁻Δ is the empty set. -/
theorem Segment.minus_eq_empty (Δ : Segment) (h : Δ.a = Δ.b) : ⁻Δ = ∅ := by
  ext n; simp [Segment.minus, interval]; omega
