module

public import FalconerThetaGauge.MaskedFourierEnergyCells

/-! # Removing genuine cell-constant masks from the actual Fourier energy -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter
open scoped Classical

namespace FalconerThetaGauge

/-- A true direction-only factor on the carrier comes out of the actual amplitude. -/
theorem maskedFourierAmplitude_eq_mul_of_eqOn (ρ : Measure Plane) {X : Set Plane}
    (hX : MeasurableSet X) (b b' : Plane → UnitCircle → ℝ) (c : UnitCircle → ℝ)
    (hfactor : ∀ x ∈ X, ∀ w, b' x w = c w * b x w) (r : ℝ) (w : UnitCircle) :
    maskedFourierAmplitude ρ X b' r w = (c w : ℂ) * maskedFourierAmplitude ρ X b r w := by
  unfold maskedFourierAmplitude
  calc
    _ = ∫ x in X, (c w : ℂ) *
        (Complex.exp (-((r * inner ℝ x (w : Plane) : ℝ) : ℂ) * Complex.I) * (b x w : ℂ)) ∂ρ := by
      apply setIntegral_congr_fun hX
      intro x hx
      dsimp only
      rw [hfactor x hx]
      simp only [Complex.ofReal_mul]
      ring
    _ = _ := integral_const_mul _ _

theorem norm_maskedFourierAmplitude_le_of_eqOn (ρ : Measure Plane) {X : Set Plane}
    (hX : MeasurableSet X) (b b' : Plane → UnitCircle → ℝ) (c : UnitCircle → ℝ)
    (hfactor : ∀ x ∈ X, ∀ w, b' x w = c w * b x w) (hc : ∀ w, |c w| ≤ 1)
    (r : ℝ) (w : UnitCircle) :
    ‖maskedFourierAmplitude ρ X b' r w‖ ≤ ‖maskedFourierAmplitude ρ X b r w‖ := by
  rw [maskedFourierAmplitude_eq_mul_of_eqOn ρ hX b b' c hfactor, norm_mul,
    Complex.norm_real, Real.norm_eq_abs]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hc w)
    (norm_nonneg (maskedFourierAmplitude ρ X b r w))

/-- Removing a bounded direction-only carrier factor increases the actual spectrum. -/
theorem maskedCircularSpectrum_le_of_eqOn (ρ : Measure Plane) [IsFiniteMeasure ρ]
    {X : Set Plane} (hX : MeasurableSet X) {b b' : Plane → UnitCircle → ℝ}
    (hb : Measurable (uncurry b)) (hb' : Measurable (uncurry b'))
    (hbound : ∀ x w, |b x w| ≤ 1) (hbound' : ∀ x w, |b' x w| ≤ 1)
    (c : UnitCircle → ℝ) (hfactor : ∀ x ∈ X, ∀ w, b' x w = c w * b x w)
    (hc : ∀ w, |c w| ≤ 1) {r : ℝ} (hr : 0 ≤ r) :
    maskedCircularSpectrum ρ X b' r ≤ maskedCircularSpectrum ρ X b r := by
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hr measureReal_nonneg)
  apply integral_mono (integrable_maskedFourier_circle_sq ρ X hb' hbound' r)
    (integrable_maskedFourier_circle_sq ρ X hb hbound r)
  intro w
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_maskedFourierAmplitude_le_of_eqOn ρ hX b b' c hfactor hc r w) 2

/-- The true dyadic energy increases when bounded cell-constant factors are removed. -/
theorem maskedFourierEnergy_le_of_eqOn (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] {X Y : Set Plane}
    (hX : MeasurableSet X) (hY : MeasurableSet Y)
    {b₁ b₂ b₁' b₂' : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂))
    (hb₁' : Measurable (uncurry b₁')) (hb₂' : Measurable (uncurry b₂'))
    (hbound₁ : ∀ x w, |b₁ x w| ≤ 1) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    (hbound₁' : ∀ x w, |b₁' x w| ≤ 1) (hbound₂' : ∀ x w, |b₂' x w| ≤ 1)
    (c₁ c₂ : UnitCircle → ℝ)
    (hfactor₁ : ∀ x ∈ X, ∀ w, b₁' x w = c₁ w * b₁ x w)
    (hfactor₂ : ∀ y ∈ Y, ∀ w, b₂' y w = c₂ w * b₂ y w)
    (hc₁ : ∀ w, |c₁ w| ≤ 1) (hc₂ : ∀ w, |c₂ w| ≤ 1) (K v : ℕ) :
    maskedFourierEnergy ρ₁ ρ₂ X Y b₁' b₂' K v ≤
      maskedFourierEnergy ρ₁ ρ₂ X Y b₁ b₂ K v := by
  have hi := integrable_maskedFourierEnergy_integrand ρ₁ ρ₂ X Y hb₁ hb₂ hbound₁ hbound₂ K v
  have hi' := integrable_maskedFourierEnergy_integrand ρ₁ ρ₂ X Y hb₁' hb₂' hbound₁' hbound₂' K v
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ ((2 : ℝ) ^ v)⁻¹)
  apply setIntegral_mono_on hi'.integrableOn hi.integrableOn measurableSet_Ioi
  intro r hr
  apply mul_le_mul_of_nonneg_left _ (maskedFrequencyCutoff_mem_Icc K _).1
  exact mul_le_mul
    (maskedCircularSpectrum_le_of_eqOn ρ₁ hX hb₁ hb₁' hbound₁ hbound₁' c₁ hfactor₁ hc₁ hr.le)
    (maskedCircularSpectrum_le_of_eqOn ρ₂ hY hb₂ hb₂' hbound₂ hbound₂' c₂ hfactor₂ hc₂ hr.le)
    (maskedCircularSpectrum_nonneg ρ₂ Y b₂' hr.le)
    (maskedCircularSpectrum_nonneg ρ₁ X b₁ hr.le)

end FalconerThetaGauge
