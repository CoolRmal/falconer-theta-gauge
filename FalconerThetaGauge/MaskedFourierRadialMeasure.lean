module

public import FalconerThetaGauge.MaskedFourierPairEnergy
public import FalconerThetaGauge.OrthogonalityRadialAmplitude
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # The genuine finite radial measure for the dyadic Fourier energy -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function

namespace FalconerThetaGauge

/-- The nonnegative radial density appearing in the literal joint square energy. -/
def maskedFourierRadialWeight (K v : ℕ) (r : ℝ) : ℝ :=
  ((2 : ℝ) ^ v)⁻¹ * maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) * r ^ 2

theorem maskedFourierRadialWeight_nonneg (K v : ℕ) (r : ℝ) :
    0 ≤ maskedFourierRadialWeight K v r := by
  exact mul_nonneg (mul_nonneg (by positivity)
    (maskedFrequencyCutoff_mem_Icc K _).1) (sq_nonneg _)

@[fun_prop]
theorem measurable_maskedFourierRadialWeight (K v : ℕ) :
    Measurable (maskedFourierRadialWeight K v) := by
  unfold maskedFourierRadialWeight
  exact (measurable_const.mul ((contDiff_maskedFrequencyCutoff K).continuous.measurable.comp
    (measurable_id.div_const _))).mul (measurable_id.pow_const 2)

theorem integrable_maskedFourierRadialWeight (K v : ℕ) :
    Integrable (maskedFourierRadialWeight K v) := by
  have hb : ∀ r ∈ Icc 0 (4 * (2 : ℝ) ^ v),
      |r ^ (2 : ℕ)| ≤ (4 * (2 : ℝ) ^ v) ^ 2 := by
    intro r hr
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ hr.1 hr.2 2
  unfold maskedFourierRadialWeight
  simpa only [mul_assoc, id_eq] using
    (integrable_maskedFrequencyCutoff_mul K v (measurable_id.pow_const 2) hb).const_mul
      (((2 : ℝ) ^ v)⁻¹)

theorem maskedFourierRadialWeight_eq_zero_of_nonpos (K v : ℕ) {r : ℝ} (hr : r ≤ 0) :
    maskedFourierRadialWeight K v r = 0 := by
  have hs : 0 < (2 : ℝ) ^ v := by positivity
  have hnot : r / (2 : ℝ) ^ v ∉ Icc (1 / 4) 4 := by
    intro hm
    have h := (le_div_iff₀ hs).mp hm.1
    have : 0 < (2 : ℝ) ^ v / 4 := by positivity
    linarith
  simp only [maskedFourierRadialWeight, maskedFrequencyCutoff_eq_zero K hnot,
    mul_zero, zero_mul]

/-- This measure is finite because its literal compactly supported density is integrable. -/
def maskedFourierRadialMeasure (K v : ℕ) : Measure ℝ :=
  volume.withDensity (fun r ↦ ENNReal.ofReal (maskedFourierRadialWeight K v r))

instance isFiniteMeasure_maskedFourierRadialMeasure (K v : ℕ) :
    IsFiniteMeasure (maskedFourierRadialMeasure K v) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_maskedFourierRadialWeight K v)
    (Filter.Eventually.of_forall (maskedFourierRadialWeight_nonneg K v))]
  exact ENNReal.ofReal_ne_top

theorem integral_maskedFourierRadialMeasure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (K v : ℕ) (f : ℝ → E) :
    (∫ r, f r ∂maskedFourierRadialMeasure K v) =
      ∫ r, maskedFourierRadialWeight K v r • f r := by
  rw [maskedFourierRadialMeasure, integral_withDensity_eq_integral_toReal_smul
    (measurable_maskedFourierRadialWeight K v).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (maskedFourierRadialWeight_nonneg K v _)]

theorem orthogonalityRadialAmplitude_eq_real_weight (K v : ℕ) (r : ℝ) :
    orthogonalityRadialAmplitude K v r = (maskedFourierRadialWeight K v r : ℂ) := by
  simp only [orthogonalityRadialAmplitude, maskedFourierRadialWeight, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_ofNat]

/-- The mass-weighted actual `F` is an integral against the genuine finite radial measure. -/
theorem mass_mul_maskedFourierEnergy_radial (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (K v : ℕ) :
    (ρ₁.real X * ρ₂.real Y) * maskedFourierEnergy ρ₁ ρ₂ X Y b₁ b₂ K v =
      ∫ r, maskedFourierPairCircleEnergy ρ₁ ρ₂ X Y b₁ b₂ r
        ∂maskedFourierRadialMeasure K v := by
  rw [mass_mul_maskedFourierEnergy ρ₁ ρ₂ X Y hb₁ hb₂ hbound₁ hbound₂,
    integral_maskedFourierRadialMeasure, ← integral_const_mul]
  simp only [smul_eq_mul, ← mul_assoc]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro r hr
  have hr' : r ≤ 0 := le_of_not_gt hr
  change maskedFourierRadialWeight K v r * _ = 0
  rw [maskedFourierRadialWeight_eq_zero_of_nonpos K v hr', zero_mul]

end FalconerThetaGauge
