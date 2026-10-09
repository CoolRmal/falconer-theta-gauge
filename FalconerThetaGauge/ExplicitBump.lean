module

public import FalconerThetaGauge.ExplicitBumpStack
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Explicit smooth even probability kernels at every finite required order

For any prescribed order `K`, convolve the first `K` uniform boxes of widths
`6/(π²j²)` with an arbitrary normalized smooth even tail in the remaining
support radius. This gives all quantitative derivative estimates through `K`
with exactly the manuscript's constants, without needing an infinite Fourier
product. The source argument uses only finitely many derivatives at each scale.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff

namespace FalconerThetaGauge

theorem explicitBoxStack_eq_zero_of_abs_gt (j K : ℕ) {R : ℝ} {f : ℝ → ℝ}
    (hf : ∀ x, R < |x| → f x = 0) {x : ℝ}
    (hx : R + ∑ i ∈ Finset.range K, explicitBoxWidth (j + i) < |x|) :
    explicitBoxStack j K f x = 0 := by
  induction K generalizing j x with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero] at hx
    exact hf x hx
  | succ K ih =>
    change boxAverage (explicitBoxWidth j) (explicitBoxStack (j + 1) K f) x = 0
    apply boxAverage_eq_zero_of_abs_gt (explicitBoxWidth_pos j)
      (R := R + ∑ i ∈ Finset.range K, explicitBoxWidth (j + 1 + i))
    · intro y hy
      exact ih (j + 1) hy
    · rw [Finset.sum_range_succ'] at hx
      simpa only [Nat.add_zero, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
        add_assoc, add_left_comm, add_comm] using hx

/-- A genuine smooth tail placed in the unused finite support radius. -/
def explicitBumpTail (K : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := explicitBumpTailRadius K / 2
  rOut := explicitBumpTailRadius K
  rIn_pos := by linarith [explicitBumpTailRadius_pos K]
  rIn_lt_rOut := by linarith [explicitBumpTailRadius_pos K]

/-- The actual order-`K` compact smooth probability kernel. -/
def explicitBump (K : ℕ) : ℝ → ℝ :=
  explicitBoxStack 0 K ((explicitBumpTail K).normed volume)

theorem contDiff_explicitBump (K : ℕ) : ContDiff ℝ ∞ (explicitBump K) :=
  contDiff_explicitBoxStack _ _ (explicitBumpTail K).contDiff_normed

theorem hasCompactSupport_explicitBump (K : ℕ) : HasCompactSupport (explicitBump K) :=
  hasCompactSupport_explicitBoxStack _ _ (explicitBumpTail K).hasCompactSupport_normed

theorem explicitBump_nonneg (K : ℕ) (x : ℝ) : 0 ≤ explicitBump K x :=
  explicitBoxStack_nonneg _ _ (explicitBumpTail K).nonneg_normed x

theorem explicitBump_even (K : ℕ) (x : ℝ) : explicitBump K (-x) = explicitBump K x :=
  explicitBoxStack_even _ _ (explicitBumpTail K).normed_neg x

theorem integral_explicitBump (K : ℕ) : (∫ x : ℝ, explicitBump K x) = 1 :=
  (integral_explicitBoxStack _ _ (explicitBumpTail K).integrable_normed).trans
    (explicitBumpTail K).integral_normed

theorem explicitBump_eq_zero_of_one_lt_abs (K : ℕ) {x : ℝ} (hx : 1 < |x|) :
    explicitBump K x = 0 := by
  apply explicitBoxStack_eq_zero_of_abs_gt (R := explicitBumpTailRadius K)
  · intro y hy
    apply notMem_support.mp
    rw [(explicitBumpTail K).support_normed_eq]
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    exact not_lt_of_ge hy.le
  · simpa only [Nat.zero_add, explicitBumpTailRadius, sub_add_cancel] using hx

theorem support_explicitBump_subset (K : ℕ) : support (explicitBump K) ⊆ Icc (-1) 1 := by
  intro x hx
  rw [mem_Icc, ← abs_le]
  by_contra h
  exact mem_support.mp hx (explicitBump_eq_zero_of_one_lt_abs K (lt_of_not_ge h))

/-- The exact uniform finite-order derivative bound needed by every cutoff at a scale. -/
theorem integral_norm_iteratedDeriv_explicitBump_le (K k : ℕ) (hk : k ≤ K) :
    (∫ x : ℝ, ‖iteratedDeriv k (explicitBump K) x‖) ≤
      (Real.pi ^ 2 / 6) ^ k * (k.factorial : ℝ) ^ 2 := by
  have h := integral_norm_iteratedDeriv_explicitBoxStack_le 0 K k hk
    (explicitBumpTail K).contDiff_normed (explicitBumpTail K).hasCompactSupport_normed
    (explicitBumpTail K).nonneg_normed (explicitBumpTail K).integral_normed
  simpa only [explicitBump, Nat.zero_add, prod_explicitBoxWidth_inv] using h

end FalconerThetaGauge
