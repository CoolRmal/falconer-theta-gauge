module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The scalar dyadic Gaussian kernel

Lemma 5.2 of the manuscript reduces its Fourier estimate to the scalar series
`K(r) = ∑ (n + 1)^γ 2^n exp(-4^n r^2)`. This module proves that series converges
at every positive radius. It does not assert the Fourier-energy inequality.
-/

@[expose] public section

open Filter
open scoped Topology

namespace FalconerThetaGauge

noncomputable section

/-- One term of the dyadic Gaussian kernel in Lemma 5.2. -/
def dyadicGaussianTerm (γ r : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ γ * (2 : ℝ) ^ n * Real.exp (-((4 : ℝ) ^ n * r ^ 2))

/-- The scalar kernel in Lemma 5.2, used at positive radii where its series converges. -/
def dyadicGaussianKernel (γ r : ℝ) : ℝ := ∑' n, dyadicGaussianTerm γ r n

theorem dyadicGaussianTerm_nonneg (γ r : ℝ) (n : ℕ) : 0 ≤ dyadicGaussianTerm γ r n := by
  unfold dyadicGaussianTerm
  positivity

theorem dyadicGaussianTerm_pos (γ r : ℝ) (n : ℕ) : 0 < dyadicGaussianTerm γ r n := by
  unfold dyadicGaussianTerm
  positivity

theorem dyadicGaussianTerm_le (γ : ℝ) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (n : ℕ) :
    dyadicGaussianTerm γ s n ≤ dyadicGaussianTerm γ r n := by
  have hsq : r ^ 2 ≤ s ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) n)
  unfold dyadicGaussianTerm
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hmul)) (by positivity)

theorem dyadicGaussianTerm_succ_le (γ r : ℝ) (hγ : 0 ≤ γ) (n : ℕ) :
    dyadicGaussianTerm γ r (n + 1) ≤
      ((2 : ℝ) ^ γ * 2 * Real.exp (-(3 * (4 : ℝ) ^ n * r ^ 2))) *
        dyadicGaussianTerm γ r n := by
  have hw : ((n : ℝ) + 1 + 1) ^ γ ≤ (2 * ((n : ℝ) + 1)) ^ γ :=
    Real.rpow_le_rpow (by positivity) (by nlinarith [Nat.cast_nonneg (α := ℝ) n]) hγ
  rw [Real.mul_rpow (by norm_num) (by positivity)] at hw
  have he : Real.exp (-((4 : ℝ) ^ n * 4 * r ^ 2)) =
      Real.exp (-((4 : ℝ) ^ n * r ^ 2)) * Real.exp (-(3 * (4 : ℝ) ^ n * r ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold dyadicGaussianTerm
  simp only [Nat.cast_add, Nat.cast_one, pow_succ (2 : ℝ), pow_succ (4 : ℝ)]
  rw [he]
  calc
    _ ≤ ((2 : ℝ) ^ γ * ((n : ℝ) + 1) ^ γ) * ((2 : ℝ) ^ n * 2) *
        (Real.exp (-((4 : ℝ) ^ n * r ^ 2)) *
          Real.exp (-(3 * (4 : ℝ) ^ n * r ^ 2))) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hw (by positivity))
        (by positivity)
    _ = _ := by ring

theorem summable_dyadicGaussianTerm (γ r : ℝ) (hγ : 0 ≤ γ) (hr : 0 < r) :
    Summable (dyadicGaussianTerm γ r) := by
  have hfour : Tendsto (fun n : ℕ ↦ (4 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hexp : Tendsto (fun n : ℕ ↦ Real.exp (-(3 * (4 : ℝ) ^ n * r ^ 2)))
      atTop (𝓝 0) := by
    convert Real.tendsto_exp_atBot.comp
      (hfour.const_mul_atTop_of_neg (by nlinarith [sq_pos_of_pos hr] : -(3 * r ^ 2) < 0))
      using 1
    ext n
    simp only [Function.comp_apply]
    congr 1
    ring
  have hfactor : Tendsto (fun n : ℕ ↦
      (2 : ℝ) ^ γ * 2 * Real.exp (-(3 * (4 : ℝ) ^ n * r ^ 2))) atTop (𝓝 0) := by
    simpa using hexp.const_mul ((2 : ℝ) ^ γ * 2)
  apply summable_of_ratio_norm_eventually_le (by norm_num : (1 / 2 : ℝ) < 1)
  filter_upwards [hfactor.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)] with n hn
  simp only [Real.norm_eq_abs, abs_of_nonneg (dyadicGaussianTerm_nonneg γ r _)]
  exact (dyadicGaussianTerm_succ_le γ r hγ n).trans
    (mul_le_mul_of_nonneg_right hn (dyadicGaussianTerm_nonneg γ r n))

theorem dyadicGaussianKernel_nonneg (γ r : ℝ) : 0 ≤ dyadicGaussianKernel γ r := by
  exact tsum_nonneg (dyadicGaussianTerm_nonneg γ r)

/-- The scalar kernel is uniformly bounded on radii at least one, as used in Lemma 5.2. -/
theorem dyadicGaussianKernel_le_at_one (γ r : ℝ) (hγ : 0 ≤ γ) (hr : 1 ≤ r) :
    dyadicGaussianKernel γ r ≤ dyadicGaussianKernel γ 1 := by
  exact Summable.tsum_le_tsum (dyadicGaussianTerm_le γ zero_le_one hr)
    (summable_dyadicGaussianTerm γ r hγ (zero_lt_one.trans_le hr))
    (summable_dyadicGaussianTerm γ 1 hγ zero_lt_one)

end

end FalconerThetaGauge
