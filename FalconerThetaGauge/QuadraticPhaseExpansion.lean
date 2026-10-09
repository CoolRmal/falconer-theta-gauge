module

public import FalconerThetaGauge.ImaginaryTaylor
public import FalconerThetaGauge.SchwartzMomentBounds
public import FalconerThetaGauge.QuadraticPhasePrefactor

/-!
# Quadratic stationary phase for actual Schwartz amplitudes

The damped Gaussian identity and the sharp imaginary Taylor remainder give
the finite stationary expansion. Every frequency moment is an actual
integrable Schwartz derivative, with no distributional identity assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset
open scoped FourierTransform

namespace FalconerThetaGauge

def quadraticTaylorCoefficient (Λ : ℝ) (j : ℕ) : ℂ :=
  (Complex.I / (2 * (Λ : ℂ))) ^ j / (j.factorial : ℂ)

theorem quadratic_fourier_taylor_term (Λ : ℝ) (j : ℕ) (ξ : ℝ) :
    (((j.factorial : ℝ)⁻¹ * (-2 * Real.pi ^ 2 / Λ * ξ ^ 2) ^ j) • Complex.I ^ j) =
      quadraticTaylorCoefficient Λ j *
        (-2 * (Real.pi : ℂ) * Complex.I * ξ) ^ (2 * j) := by
  have hid : (((-2 * Real.pi ^ 2 / Λ * ξ ^ 2 : ℝ) : ℂ) * Complex.I) =
      (Complex.I / (2 * (Λ : ℂ))) *
        (-2 * (Real.pi : ℂ) * Complex.I * ξ) ^ 2 := by
    push_cast
    field_simp
    simp only [Complex.I_sq]
    ring
  calc
    _ = (j.factorial : ℂ)⁻¹ *
        (((-2 * Real.pi ^ 2 / Λ * ξ ^ 2 : ℝ) : ℂ) * Complex.I) ^ j := by
      simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv,
        Complex.ofReal_natCast, Complex.ofReal_pow, mul_pow]
      ring
    _ = _ := by rw [hid, mul_pow, ← pow_mul]; simp [quadraticTaylorCoefficient]; ring

theorem quadratic_dual_argument_abs {Λ : ℝ} (hΛ : 0 < Λ) (ξ : ℝ) :
    |(-2 * Real.pi ^ 2 / Λ * ξ ^ 2)| =
      ‖-2 * (Real.pi : ℂ) * Complex.I * ξ‖ ^ 2 / (2 * Λ) := by
  have hn : -2 * Real.pi ^ 2 / Λ * ξ ^ 2 ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg Real.pi]) hΛ.le)
      (sq_nonneg _)
  rw [abs_of_nonpos hn, norm_quadraticFrequency_sq]
  field_simp

theorem integrable_quadraticFourierTaylorTerm (Λ : ℝ) (j : ℕ)
    (g : SchwartzMap ℝ ℂ) :
    Integrable (fun ξ : ℝ ↦ quadraticTaylorCoefficient Λ j *
      ((-2 * (Real.pi : ℂ) * Complex.I * ξ) ^ (2 * j) * (𝓕⁻ g) ξ)) := by
  have h := (𝓕⁻ (schwartzIteratedDeriv (2 * j) g)).integrable (μ := volume)
  simpa only [fourierInv_schwartzIteratedDeriv] using h.const_mul _

theorem integral_quadraticFourierTaylorSum (Λ : ℝ) (T : ℕ) (g : SchwartzMap ℝ ℂ) :
    (∫ ξ : ℝ, ∑ j ∈ range T, quadraticTaylorCoefficient Λ j *
      ((-2 * (Real.pi : ℂ) * Complex.I * ξ) ^ (2 * j) * (𝓕⁻ g) ξ)) =
      ∑ j ∈ range T, quadraticTaylorCoefficient Λ j * iteratedDeriv (2 * j) g 0 := by
  rw [integral_finsetSum (range T) (fun j _ ↦ integrable_quadraticFourierTaylorTerm Λ j g)]
  apply sum_congr rfl
  intro j _
  rw [integral_const_mul, integral_fourierInv_derivative_moment]

def quadraticFourierRemainder (Λ : ℝ) (T : ℕ) (g : SchwartzMap ℝ ℂ) (ξ : ℝ) : ℂ :=
  (imaginaryExponential (-2 * Real.pi ^ 2 / Λ * ξ ^ 2) -
    ∑ j ∈ range T,
      ((j.factorial : ℝ)⁻¹ * (-2 * Real.pi ^ 2 / Λ * ξ ^ 2) ^ j) • Complex.I ^ j) *
    (𝓕⁻ g) ξ

theorem quadraticFourierRemainder_eq (Λ : ℝ) (T : ℕ) (g : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    quadraticFourierRemainder Λ T g ξ =
      imaginaryExponential (-2 * Real.pi ^ 2 / Λ * ξ ^ 2) * (𝓕⁻ g) ξ -
        ∑ j ∈ range T, quadraticTaylorCoefficient Λ j *
          ((-2 * (Real.pi : ℂ) * Complex.I * ξ) ^ (2 * j) * (𝓕⁻ g) ξ) := by
  rw [quadraticFourierRemainder, sub_mul, sum_mul]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [quadratic_fourier_taylor_term, mul_assoc]

theorem norm_quadraticFourierRemainder_le {Λ : ℝ} (hΛ : 0 < Λ) (T : ℕ)
    (g : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    ‖quadraticFourierRemainder Λ T g ξ‖ ≤
      (2 * Λ)⁻¹ ^ T / (T.factorial : ℝ) *
        ‖(-2 * (Real.pi : ℂ) * Complex.I * ξ) ^ (2 * T) * (𝓕⁻ g) ξ‖ := by
  unfold quadraticFourierRemainder
  rw [norm_mul]
  have h := mul_le_mul_of_nonneg_right
    (norm_imaginaryExponential_sub_sum_le (-2 * Real.pi ^ 2 / Λ * ξ ^ 2) T)
    (norm_nonneg ((𝓕⁻ g) ξ))
  refine h.trans_eq ?_
  rw [quadratic_dual_argument_abs hΛ, div_pow, pow_mul]
  simp only [norm_mul, norm_pow, div_eq_mul_inv, inv_pow]
  ring

theorem integrable_quadraticDualPhase (Λ : ℝ) (g : SchwartzMap ℝ ℂ) :
    Integrable (fun ξ : ℝ ↦
      imaginaryExponential (-2 * Real.pi ^ 2 / Λ * ξ ^ 2) * (𝓕⁻ g) ξ) := by
  apply ((𝓕⁻ g).integrable (μ := volume)).bdd_mul
  · exact (contDiff_imaginaryExponential.continuous.comp
      (by fun_prop)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun ξ ↦ (norm_imaginaryExponential _).le

theorem integrable_quadraticFourierRemainder (Λ : ℝ) (T : ℕ) (g : SchwartzMap ℝ ℂ) :
    Integrable (quadraticFourierRemainder Λ T g) := by
  have hsum := integrable_finsetSum (range T)
    (fun j _ ↦ integrable_quadraticFourierTaylorTerm Λ j g)
  change Integrable (fun ξ : ℝ ↦ quadraticFourierRemainder Λ T g ξ)
  simp_rw [quadraticFourierRemainder_eq]
  exact (integrable_quadraticDualPhase Λ g).sub hsum

theorem integral_quadraticFourierRemainder (Λ : ℝ) (T : ℕ) (g : SchwartzMap ℝ ℂ) :
    (∫ ξ : ℝ, quadraticFourierRemainder Λ T g ξ) =
      (∫ ξ : ℝ, imaginaryExponential (-2 * Real.pi ^ 2 / Λ * ξ ^ 2) * (𝓕⁻ g) ξ) -
        ∑ j ∈ range T, quadraticTaylorCoefficient Λ j * iteratedDeriv (2 * j) g 0 := by
  simp_rw [quadraticFourierRemainder_eq]
  rw [integral_sub (integrable_quadraticDualPhase Λ g)
    (integrable_finsetSum (range T)
      (fun j _ ↦ integrable_quadraticFourierTaylorTerm Λ j g)),
    integral_quadraticFourierTaylorSum]

theorem norm_integral_quadraticFourierRemainder_le {Λ : ℝ} (hΛ : 0 < Λ) (T : ℕ)
    (g : SchwartzMap ℝ ℂ) :
    ‖∫ ξ : ℝ, quadraticFourierRemainder Λ T g ξ‖ ≤
      (2 * Λ)⁻¹ ^ T / (T.factorial : ℝ) *
        ((∫ x : ℝ, ‖iteratedDeriv (2 * T) g x‖) +
          (∫ x : ℝ, ‖iteratedDeriv (2 * T + 2) g x‖)) / 2 := by
  have hmoment : Integrable (fun ξ : ℝ ↦
      ‖(-2 * (Real.pi : ℂ) * Complex.I * ξ) ^ (2 * T) * (𝓕⁻ g) ξ‖) := by
    simpa only [fourierInv_schwartzIteratedDeriv] using
      (𝓕⁻ (schwartzIteratedDeriv (2 * T) g)).integrable.norm (μ := volume)
  calc
    _ ≤ ∫ ξ : ℝ, ‖quadraticFourierRemainder Λ T g ξ‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ ξ : ℝ, (2 * Λ)⁻¹ ^ T / (T.factorial : ℝ) *
        ‖(-2 * (Real.pi : ℂ) * Complex.I * ξ) ^ (2 * T) * (𝓕⁻ g) ξ‖ :=
      integral_mono (integrable_quadraticFourierRemainder Λ T g).norm
        (hmoment.const_mul _) (norm_quadraticFourierRemainder_le hΛ T g)
    _ = (2 * Λ)⁻¹ ^ T / (T.factorial : ℝ) *
        ∫ ξ : ℝ, ‖(-2 * (Real.pi : ℂ) * Complex.I * ξ) ^ (2 * T) * (𝓕⁻ g) ξ‖ :=
      integral_const_mul _ _
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (integral_fourierInv_derivative_power_le (2 * T) g)
        (by positivity : 0 ≤ (2 * Λ)⁻¹ ^ T / (T.factorial : ℝ))
      convert h using 1
      ring

/-- The actual stationary expansion, with its sharp derivative remainder. -/
theorem quadratic_phase_expansion_norm {Λ : ℝ} (hΛ : 0 < Λ) (T : ℕ)
    (g : SchwartzMap ℝ ℂ) :
    ‖(∫ s : ℝ, Complex.exp (((Λ / 2 * s ^ 2 : ℝ) : ℂ) * Complex.I) * g s) -
      quadraticPhasePrefactor Λ *
        ∑ j ∈ range T, quadraticTaylorCoefficient Λ j * iteratedDeriv (2 * j) g 0‖ ≤
      ‖quadraticPhasePrefactor Λ‖ / 2 * (2 * Λ)⁻¹ ^ T / (T.factorial : ℝ) *
        ((∫ x : ℝ, ‖iteratedDeriv (2 * T) g x‖) +
          (∫ x : ℝ, ‖iteratedDeriv (2 * T + 2) g x‖)) := by
  rw [quadratic_phase_fourier_identity hΛ]
  have hphase : ∀ ξ : ℝ,
      Complex.exp (-((2 * Real.pi ^ 2 / Λ * ξ ^ 2 : ℝ) : ℂ) * Complex.I) =
        imaginaryExponential (-2 * Real.pi ^ 2 / Λ * ξ ^ 2) := by
    intro ξ
    unfold imaginaryExponential
    congr 1
    push_cast
    ring
  simp_rw [hphase]
  rw [← mul_sub, ← integral_quadraticFourierRemainder, norm_mul]
  have h := mul_le_mul_of_nonneg_left (norm_integral_quadraticFourierRemainder_le hΛ T g)
    (norm_nonneg (quadraticPhasePrefactor Λ))
  convert h using 1
  ring

/-- Lemma 3.5 for Schwartz amplitudes, with the manuscript's exact prefactor and bound. -/
theorem quadratic_phase_expansion {Λ : ℝ} (hΛ : 0 < Λ) (T : ℕ)
    (g : SchwartzMap ℝ ℂ) :
    ‖(∫ s : ℝ, Complex.exp (((Λ / 2 * s ^ 2 : ℝ) : ℂ) * Complex.I) * g s) -
      (Real.sqrt (2 * Real.pi / Λ) : ℂ) *
        Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
          ∑ j ∈ range T, quadraticTaylorCoefficient Λ j * iteratedDeriv (2 * j) g 0‖ ≤
      Real.sqrt (2 / Λ) * (2 * Λ)⁻¹ ^ T / (T.factorial : ℝ) *
        ((∫ x : ℝ, ‖iteratedDeriv (2 * T) g x‖) +
          (∫ x : ℝ, ‖iteratedDeriv (2 * T + 2) g x‖)) := by
  rw [← quadraticPhasePrefactor_eq hΛ]
  refine (quadratic_phase_expansion_norm hΛ T g).trans ?_
  have hnonneg : 0 ≤ (2 * Λ)⁻¹ ^ T / (T.factorial : ℝ) *
      ((∫ x : ℝ, ‖iteratedDeriv (2 * T) g x‖) +
        (∫ x : ℝ, ‖iteratedDeriv (2 * T + 2) g x‖)) := by
    apply mul_nonneg (by positivity)
    exact add_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)
      (integral_nonneg fun _ ↦ norm_nonneg _)
  have h := mul_le_mul_of_nonneg_right (norm_quadraticPhasePrefactor_half_le hΛ) hnonneg
  convert h using 1 <;> ring

end FalconerThetaGauge
