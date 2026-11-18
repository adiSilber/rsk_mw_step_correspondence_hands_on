import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import LeanProof.Fundamentals_t

/-! # Functional-equation pairs (trusted definitions)

Mathlib's `WeakFEPair ℂ` is the device behind the meromorphic continuation: two functions `f`,
`g` on `(0, ∞)` with `f (1/x) = ε · x^k · g x`, each approaching a constant (`f₀`, `g₀`) faster
than every power at `∞`; its `Λ` is the Mellin transform of `f` with the two poles removed.
Mathlib bundles the six pieces of data with seven proofs. Here the data is a structure of its own,
the seven facts are one proposition, and `WeakFEPair.ofData` packs data and facts into Mathlib's
structure. The facts are proved in `_u` files and omitted where a pair is assembled (`Theta2_t`). -/

noncomputable section
open MeasureTheory

/-- The data of a functional-equation pair: `WeakFEPair ℂ` without its proofs. -/
structure PairData where
  /-- The function whose Mellin transform is studied. -/
  f : ℝ → ℂ
  /-- Its partner under `x ↦ 1/x`. -/
  g : ℝ → ℂ
  /-- The weight: `f (1/x) = ε · x^k · g x`. -/
  k : ℝ
  /-- The root number. -/
  ε : ℂ
  /-- The constant term of `f` at `∞`. -/
  f₀ : ℂ
  /-- The constant term of `g` at `∞`. -/
  g₀ : ℂ

/-- The seven facts Mathlib asks of the data, as it states them: `f` and `g` locally integrable on
`(0, ∞)`, `k > 0`, `ε ≠ 0`, the functional equation, and `f - f₀`, `g - g₀` smaller than every
power of `x` at `∞`. -/
structure PairData.Valid (d : PairData) : Prop where
  hf_int : LocallyIntegrableOn d.f (0, ∞)
  hg_int : LocallyIntegrableOn d.g (0, ∞)
  hk : 0 < d.k
  hε : d.ε ≠ 0
  h_feq : ∀ x ∈ (0, ∞), d.f (1 / x) = d.ε * x ^ d.k * d.g x
  hf_top : ∀ r : ℝ, (fun x ↦ d.f x - d.f₀) =O (fun x ↦ x ^ r)
  hg_top : ∀ r : ℝ, (fun x ↦ d.g x - d.g₀) =O (fun x ↦ x ^ r)

/-- Mathlib's pair, from data and its facts. -/
def WeakFEPair.ofData (d : PairData) (h : d.Valid) : WeakFEPair ℂ where
  f := d.f
  g := d.g
  k := d.k
  ε := d.ε
  f₀ := d.f₀
  g₀ := d.g₀
  hf_int := h.hf_int
  hg_int := h.hg_int
  hk := h.hk
  hε := h.hε
  h_feq := h.h_feq
  hf_top := h.hf_top
  hg_top := h.hg_top

/-- The data of a Mathlib pair. -/
def WeakFEPair.data (P : WeakFEPair ℂ) : PairData where
  f := P.f
  g := P.g
  k := P.k
  ε := P.ε
  f₀ := P.f₀
  g₀ := P.g₀

end
