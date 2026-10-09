module

public import FalconerThetaGauge.OrliczEnergyFourierGaussian
public import FalconerThetaGauge.OrliczEnergyFourierKernel

/-!
# Logarithmically weighted Gaussian Fourier energy

The Gaussian Fourier identity is lifted to nonnegative extended integrals.
Tonelli then bounds the logarithmically weighted dyadic frequency series by
the actual spatial critical logarithmic energy.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace FalconerThetaGauge

theorem integrable_planarGaussian_fourier_energy (μ : Measure Plane)
    [IsProbabilityMeasure μ] {b : ℝ} (hb : 0 < b) :
    Integrable (fun ξ : Plane ↦ Real.exp (-b * ‖ξ‖ ^ 2) *
      ‖planarMeasureFourier μ ξ‖ ^ 2) volume := by
  have hg : Integrable (fun ξ : Plane ↦ Real.exp (-b * ‖ξ‖ ^ 2)) volume := by
    have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (by exact hb : 0 < (b : ℂ).re) 0 (0 : Plane)
    have he (ξ : Plane) :
        (Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2 +
          0 * ((inner ℝ (0 : Plane) ξ : ℝ) : ℂ))).re = Real.exp (-b * ‖ξ‖ ^ 2) := by
      simp only [zero_mul, add_zero]
      rw [show -(b : ℂ) * ‖ξ‖ ^ 2 = ((-b * ‖ξ‖ ^ 2 : ℝ) : ℂ) by push_cast; rfl,
        ← Complex.ofReal_exp, Complex.ofReal_re]
    have h' := h.re
    change Integrable (fun ξ : Plane ↦
      (Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2 +
        0 * ((inner ℝ (0 : Plane) ξ : ℝ) : ℂ))).re) volume at h'
    simpa only [he] using h'
  apply hg.mono' (by fun_prop)
  exact Eventually.of_forall fun ξ ↦ by
    have hchar : ‖planarMeasureFourier μ ξ‖ ^ 2 ≤ 1 := by
      rw [norm_planarMeasureFourier]
      nlinarith [norm_charFun_le_one (μ := μ) ξ, norm_nonneg (charFun μ ξ)]
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ Real.exp (-b * ‖ξ‖ ^ 2) * ‖planarMeasureFourier μ ξ‖ ^ 2), mul_one] using
      mul_le_mul_of_nonneg_left hchar (Real.exp_nonneg _)

theorem integrable_planarGaussian_spatial (μ : Measure Plane) [IsFiniteMeasure μ]
    {b : ℝ} (hb : 0 < b) :
    Integrable (fun p : Plane × Plane ↦ Real.exp (-(‖p.1 - p.2‖ ^ 2 / (4 * b))))
      (μ.prod μ) := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  exact Eventually.of_forall fun p ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))

/-- Extended nonnegative Gaussian duality in the manuscript's normalization. -/
theorem lintegral_planarGaussian_fourier_energy (μ : Measure Plane)
    [IsProbabilityMeasure μ] {b : ℝ} (hb : 0 < b) :
    ∫⁻ ξ : Plane, ENNReal.ofReal (Real.exp (-b * ‖ξ‖ ^ 2) *
      ‖planarMeasureFourier μ ξ‖ ^ 2) =
      ENNReal.ofReal (Real.pi / b) * ∫⁻ p : Plane × Plane,
        ENNReal.ofReal (Real.exp (-(‖p.1 - p.2‖ ^ 2 / (4 * b)))) ∂μ.prod μ := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_planarGaussian_fourier_energy μ hb) (Eventually.of_forall fun _ ↦ by positivity),
    integral_planarGaussian_fourier_norm_sq μ hb,
    ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal (integrable_planarGaussian_spatial μ hb)
      (Eventually.of_forall fun _ ↦ by positivity)]

/-- The frequency Gaussian at dyadic scale, with logarithmic coefficient. -/
def dyadicGaussianFourierTerm (γ : ℝ) (μ : Measure Plane) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((n : ℝ) + 1) ^ γ / (2 : ℝ) ^ n) *
    ∫⁻ ξ : Plane, ENNReal.ofReal (Real.exp (-(‖ξ‖ ^ 2 / (4 : ℝ) ^ (n + 1))) *
      ‖planarMeasureFourier μ ξ‖ ^ 2)

theorem dyadicGaussianFourierTerm_eq (γ : ℝ) (μ : Measure Plane)
    [IsProbabilityMeasure μ] (n : ℕ) :
    dyadicGaussianFourierTerm γ μ n = ENNReal.ofReal (4 * Real.pi) *
      ∫⁻ p : Plane × Plane, ENNReal.ofReal (dyadicGaussianTerm γ (dist p.1 p.2) n)
        ∂μ.prod μ := by
  have h₄ : (4 : ℝ) ^ n ≠ 0 := by positivity
  have h₂ : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hfour : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  have h := lintegral_planarGaussian_fourier_energy μ
    (show 0 < 1 / (4 : ℝ) ^ (n + 1) by positivity)
  have hf (ξ : Plane) : -(1 / (4 : ℝ) ^ (n + 1)) * ‖ξ‖ ^ 2 =
      -(‖ξ‖ ^ 2 / (4 : ℝ) ^ (n + 1)) := by ring
  have hp (p : Plane × Plane) :
      -(‖p.1 - p.2‖ ^ 2 / (4 * (1 / (4 : ℝ) ^ (n + 1)))) =
        -((4 : ℝ) ^ n * (dist p.1 p.2) ^ 2) := by
    rw [dist_eq_norm, pow_succ]
    field_simp
    ring
  simp_rw [hf, hp] at h
  rw [dyadicGaussianFourierTerm, h]
  have hcoeff : (((n : ℝ) + 1) ^ γ / (2 : ℝ) ^ n) *
      (Real.pi / (1 / (4 : ℝ) ^ (n + 1))) =
        (4 * Real.pi) * (((n : ℝ) + 1) ^ γ * (2 : ℝ) ^ n) := by
    rw [pow_succ, hfour]
    field_simp
  have hn : 0 ≤ ((n : ℝ) + 1) ^ γ * (2 : ℝ) ^ n := by positivity
  simp_rw [dyadicGaussianTerm, ENNReal.ofReal_mul hn]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), hcoeff,
    ENNReal.ofReal_mul (by positivity), mul_assoc]

theorem tsum_dyadicGaussianFourierTerm_eq (γ : ℝ) (μ : Measure Plane)
    [IsProbabilityMeasure μ] :
    ∑' n, dyadicGaussianFourierTerm γ μ n = ENNReal.ofReal (4 * Real.pi) *
      ∫⁻ p : Plane × Plane, ennDyadicGaussianKernel γ (dist p.1 p.2) ∂μ.prod μ := by
  simp_rw [dyadicGaussianFourierTerm_eq]
  rw [ENNReal.tsum_mul_left, ← lintegral_tsum (fun n ↦ by
    unfold dyadicGaussianTerm
    fun_prop)]
  rfl

/-- The genuine logarithmically weighted Fourier Gaussian series is controlled by
the critical logarithmic spatial energy, with a constant depending only on γ. -/
theorem tsum_dyadicGaussianFourierTerm_le (γ : ℝ) (hγ : 0 ≤ γ) (μ : Measure Plane)
    [IsProbabilityMeasure μ] :
    ∑' n, dyadicGaussianFourierTerm γ μ n ≤
      ENNReal.ofReal (4 * Real.pi * dyadicGaussianEnergyConstant γ) *
        (1 + logCriticalEnergy γ μ) := by
  rw [tsum_dyadicGaussianFourierTerm_eq,
    show ENNReal.ofReal (4 * Real.pi * dyadicGaussianEnergyConstant γ) =
      ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (dyadicGaussianEnergyConstant γ) from
        ENNReal.ofReal_mul (by positivity),
    mul_assoc, logCriticalEnergy_eq_lintegral_prod]
  apply mul_le_mul' le_rfl
  calc
    ∫⁻ p : Plane × Plane, ennDyadicGaussianKernel γ (dist p.1 p.2) ∂μ.prod μ ≤
        ∫⁻ p : Plane × Plane, ENNReal.ofReal (dyadicGaussianEnergyConstant γ) *
          (1 + logCriticalKernel γ p.1 p.2) ∂μ.prod μ :=
      lintegral_mono fun p ↦ ennDyadicGaussianKernel_le γ _ hγ dist_nonneg
    _ = ENNReal.ofReal (dyadicGaussianEnergyConstant γ) *
        (1 + ∫⁻ p : Plane × Plane, logCriticalKernel γ p.1 p.2 ∂μ.prod μ) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left measurable_const]
      simp

theorem tsum_dyadicGaussianFourierTerm_ne_top (γ : ℝ) (hγ : 0 ≤ γ)
    (μ : Measure Plane) [IsProbabilityMeasure μ]
    (henergy : logCriticalEnergy γ μ ≠ ∞) :
    (∑' n, dyadicGaussianFourierTerm γ μ n) ≠ ∞ := by
  exact ne_top_of_le_ne_top (by finiteness)
    (tsum_dyadicGaussianFourierTerm_le γ hγ μ)

end FalconerThetaGauge
