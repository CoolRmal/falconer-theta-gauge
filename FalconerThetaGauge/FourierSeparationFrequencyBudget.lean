/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierSeparationInverseKernel
public import FalconerThetaGauge.StationaryPhaseInverseOperatorBudget

/-! # Uniform frequency coefficient costs for the actual inverse circle series -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric Polynomial Finset
open scoped Classical ContDiff

namespace FalconerThetaGauge

def scheduledPairFrequencyCoefficient (p : Polynomial ℂ) (j : ℕ)
    (d₁ d₂ : ScheduledSymbolData) (E : ℝ) (I₁ I₂ : Finset ProfileScheduleTest)
    (x₀ y₀ : Plane) (ρ r : ℝ) (z : ScheduledPairOperatorBranch p I₁ I₂ × ℕ) : ℂ :=
  (r : ℂ)⁻¹ ^ j * scheduledPairSeparatedCoefficient p j d₁ d₂ E I₁ I₂ x₀ y₀ ρ z

def scheduledPairFrequencyMajorant (p : Polynomial ℂ) (j : ℕ)
    (d₁ d₂ : ScheduledSymbolData) (E : ℝ) (I₁ I₂ : Finset ProfileScheduleTest)
    (x₀ y₀ : Plane) (ρ R : ℝ) (z : ScheduledPairOperatorBranch p I₁ I₂ × ℕ) : ℝ :=
  R⁻¹ ^ j * ‖scheduledPairSeparatedCoefficient p j d₁ d₂ E I₁ I₂ x₀ y₀ ρ z‖

@[fun_prop]
theorem measurable_scheduledPairFrequencyCoefficient (p : Polynomial ℂ) (j : ℕ)
    (d₁ d₂ : ScheduledSymbolData) (E : ℝ) (I₁ I₂ : Finset ProfileScheduleTest)
    (x₀ y₀ : Plane) (ρ : ℝ) (z : ScheduledPairOperatorBranch p I₁ I₂ × ℕ) :
    Measurable (fun r ↦
      scheduledPairFrequencyCoefficient p j d₁ d₂ E I₁ I₂ x₀ y₀ ρ r z) := by
  unfold scheduledPairFrequencyCoefficient
  fun_prop

theorem norm_scheduledPairFrequencyCoefficient_le (p : Polynomial ℂ) (j : ℕ)
    (d₁ d₂ : ScheduledSymbolData) (E : ℝ) (I₁ I₂ : Finset ProfileScheduleTest)
    (x₀ y₀ : Plane) (ρ : ℝ) {R r : ℝ} (hR : 0 < R) (hRr : R ≤ r)
    (z : ScheduledPairOperatorBranch p I₁ I₂ × ℕ) :
    ‖scheduledPairFrequencyCoefficient p j d₁ d₂ E I₁ I₂ x₀ y₀ ρ r z‖ ≤
      scheduledPairFrequencyMajorant p j d₁ d₂ E I₁ I₂ x₀ y₀ ρ R z := by
  have hr : 0 < r := hR.trans_le hRr
  rw [scheduledPairFrequencyCoefficient, norm_mul, norm_pow, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr.le]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (inv_nonneg.mpr hr.le) (inv_anti₀ hR hRr) j) (norm_nonneg _)

theorem summable_scheduledPairFrequencyMajorant (p : Polynomial ℂ) (j : ℕ)
    (d₁ d₂ : ScheduledSymbolData) (E : ℝ) (I₁ I₂ : Finset ProfileScheduleTest)
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀) (R : ℝ) :
    Summable (scheduledPairFrequencyMajorant p j d₁ d₂ E I₁ I₂ x₀ y₀ ρ R) :=
  (summable_norm_scheduledPairSeparatedCoefficient p j d₁ d₂ E I₁ I₂ hρ hsep).mul_left _

theorem polynomialWeightedNorm_mono_scale (p : Polynomial ℂ) {M M' : ℝ}
    (hM : 0 ≤ M) (hMM' : M ≤ M') : polynomialWeightedNorm p M ≤
      polynomialWeightedNorm p M' := by
  apply sum_le_sum
  intro n _
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM hMM' n) (norm_nonneg _)

theorem tsum_scheduledPairFrequencyMajorant_inverse_le {j T : ℕ} (hj : j ≤ T)
    (d₁ d₂ : ScheduledSymbolData) (E : ℝ) (I₁ I₂ : Finset ProfileScheduleTest)
    {L₁ L₂ : ℕ} (hL₁ : ∀ test ∈ I₁, test.length ≤ L₁)
    (hL₂ : ∀ test ∈ I₂, test.length ≤ L₂)
    (horder₁ : d₁.order I₁ + 2 * j ≤ 8 * T)
    (horder₂ : d₂.order I₂ + 2 * j ≤ 8 * T) {M : ℝ} (hM : 1 ≤ M)
    (hM₁ : scheduledSymbolScale T E I₁ L₁ ≤ M)
    (hM₂ : scheduledSymbolScale T E I₂ L₂ ≤ M)
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    {C R : ℝ} (hC : Real.sqrt 2 / dist x₀ y₀ ≤ C) (hR : 0 < R) :
    (∑' z : ScheduledPairOperatorBranch (stationaryPhaseInversePolynomial j) I₁ I₂ × ℕ,
      scheduledPairFrequencyMajorant (stationaryPhaseInversePolynomial j) j
        d₁ d₂ E I₁ I₂ x₀ y₀ ρ R z) ≤ (800 * T * M ^ 2 * C / R) ^ j := by
  have hdeg := stationaryPhaseInversePolynomial_natDegree_le j
  have hscale : 0 ≤ scheduledSymbolScale T E I₁ L₁ +
      scheduledSymbolScale T E I₂ L₂ :=
    add_nonneg (scheduledSymbolScale_nonneg _ _ _ _) (scheduledSymbolScale_nonneg _ _ _ _)
  have hscaleM : scheduledSymbolScale T E I₁ L₁ +
      scheduledSymbolScale T E I₂ L₂ ≤ 2 * M :=
    (add_le_add hM₁ hM₂).trans_eq (by ring)
  have hQ : polynomialWeightedNorm (stationaryPhaseInversePolynomial j)
      (scheduledSymbolScale T E I₁ L₁ + scheduledSymbolScale T E I₂ L₂) ≤
        (800 * T * M ^ 2) ^ j := by
    apply (polynomialWeightedNorm_mono_scale _ hscale hscaleM).trans
    convert stationaryPhaseInversePolynomial_weightedNorm_uniform
      (by linarith : 1 ≤ 2 * M) T hj using 1
    ring
  have hC₀ : 0 ≤ C := (div_nonneg (Real.sqrt_nonneg _) (dist_nonneg)).trans hC
  calc
    _ = R⁻¹ ^ j * ∑' z :
        ScheduledPairOperatorBranch (stationaryPhaseInversePolynomial j) I₁ I₂ × ℕ,
          ‖scheduledPairSeparatedCoefficient (stationaryPhaseInversePolynomial j) j
            d₁ d₂ E I₁ I₂ x₀ y₀ ρ z‖ := by
      exact tsum_mul_left
    _ ≤ R⁻¹ ^ j * (polynomialWeightedNorm (stationaryPhaseInversePolynomial j)
        (scheduledSymbolScale T E I₁ L₁ + scheduledSymbolScale T E I₂ L₂) *
          (Real.sqrt 2 / dist x₀ y₀) ^ j) :=
      mul_le_mul_of_nonneg_left
        (tsum_norm_scheduledPairSeparatedCoefficient_le _ j d₁ d₂ E I₁ I₂ hL₁ hL₂
          (by omega) (by omega) hρ hsep) (by positivity)
    _ ≤ R⁻¹ ^ j * ((800 * T * M ^ 2) ^ j * C ^ j) := by
      gcongr
    _ = _ := by rw [← mul_pow, ← mul_pow]; congr 1; field_simp

theorem tsum_scheduledPairFrequencyMajorant_inverse_dyadic_le {j T : ℕ} (hj : j ≤ T)
    (d₁ d₂ : ScheduledSymbolData) (E : ℝ) (I₁ I₂ : Finset ProfileScheduleTest)
    {L₁ L₂ : ℕ} (hL₁ : ∀ test ∈ I₁, test.length ≤ L₁)
    (hL₂ : ∀ test ∈ I₂, test.length ≤ L₂)
    (horder₁ : d₁.order I₁ + 2 * j ≤ 8 * T)
    (horder₂ : d₂.order I₂ + 2 * j ≤ 8 * T) {M : ℝ} (hM : 1 ≤ M)
    (hM₁ : scheduledSymbolScale T E I₁ L₁ ≤ M)
    (hM₂ : scheduledSymbolScale T E I₂ L₂ ≤ M)
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    (a v : ℝ) (hC : Real.sqrt 2 / dist x₀ y₀ ≤ 6 * (2 : ℝ) ^ a) :
    (∑' z : ScheduledPairOperatorBranch (stationaryPhaseInversePolynomial j) I₁ I₂ × ℕ,
      scheduledPairFrequencyMajorant (stationaryPhaseInversePolynomial j) j
        d₁ d₂ E I₁ I₂ x₀ y₀ ρ ((2 : ℝ) ^ v / 2) z) ≤
      (9600 * T * M ^ 2 * (2 : ℝ) ^ (a - v)) ^ j := by
  have hv : 0 < (2 : ℝ) ^ v := Real.rpow_pos_of_pos (by norm_num) _
  have h := tsum_scheduledPairFrequencyMajorant_inverse_le (R := (2 : ℝ) ^ v / 2)
    hj d₁ d₂ E I₁ I₂ hL₁ hL₂
    horder₁ horder₂ hM hM₁ hM₂ hρ hsep hC (div_pos hv (by norm_num))
  have he : (800 * T * M ^ 2 * (6 * (2 : ℝ) ^ a) / ((2 : ℝ) ^ v / 2)) =
      9600 * T * M ^ 2 * (2 : ℝ) ^ (a - v) := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    field_simp
    ring
  simpa only [he] using h

end FalconerThetaGauge
