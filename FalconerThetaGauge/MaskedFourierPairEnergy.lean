module

public import FalconerThetaGauge.MaskedFourierEnergyAverage
public import FalconerThetaGauge.MaskedFourierCells
public import Mathlib.MeasureTheory.Integral.Prod

/-! # The actual two-circle square energy and its carrier-mass normalization -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function

namespace FalconerThetaGauge

/-- The literal joint angular square of the two actual masked amplitudes. -/
def maskedFourierPairCircleEnergy (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    (b₁ b₂ : Plane → UnitCircle → ℝ) (r : ℝ) : ℝ :=
  ∫ w : UnitCircle × UnitCircle,
    ‖maskedFourierAmplitude ρ₁ X b₁ r w.1 * maskedFourierAmplitude ρ₂ Y b₂ r w.2‖ ^ 2
      ∂circleArcLength.prod circleArcLength

theorem maskedFourierPairCircleEnergy_eq (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    (b₁ b₂ : Plane → UnitCircle → ℝ) (r : ℝ) :
    maskedFourierPairCircleEnergy ρ₁ ρ₂ X Y b₁ b₂ r =
      (∫ w, ‖maskedFourierAmplitude ρ₁ X b₁ r w‖ ^ 2 ∂circleArcLength) *
        ∫ w, ‖maskedFourierAmplitude ρ₂ Y b₂ r w‖ ^ 2 ∂circleArcLength := by
  unfold maskedFourierPairCircleEnergy
  simp_rw [norm_mul, mul_pow]
  exact integral_prod_mul
    (fun w ↦ ‖maskedFourierAmplitude ρ₁ X b₁ r w‖ ^ 2)
    (fun w ↦ ‖maskedFourierAmplitude ρ₂ Y b₂ r w‖ ^ 2)

theorem integrable_maskedFourierPairCircleEnergy (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (r : ℝ) :
    Integrable (fun w : UnitCircle × UnitCircle ↦
      ‖maskedFourierAmplitude ρ₁ X b₁ r w.1 * maskedFourierAmplitude ρ₂ Y b₂ r w.2‖ ^ 2)
      (circleArcLength.prod circleArcLength) := by
  simpa only [norm_mul, mul_pow] using
    (integrable_maskedFourier_circle_sq ρ₁ X hb₁ hbound₁ r).mul_prod
      (integrable_maskedFourier_circle_sq ρ₂ Y hb₂ hbound₂ r)

/-- Carrier mass cancels the normalization even when the actual carrier has mass zero. -/
theorem mass_mul_maskedCircularSpectrum (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (X : Set Plane) {b : Plane → UnitCircle → ℝ} (hb : Measurable (uncurry b))
    (hbound : ∀ x w, |b x w| ≤ 1) (r : ℝ) :
    ρ.real X * maskedCircularSpectrum ρ X b r =
      r * ∫ w, ‖maskedFourierAmplitude ρ X b r w‖ ^ 2 ∂circleArcLength := by
  by_cases hX : ρ.real X = 0
  · simp [hX, maskedFourierAmplitude_eq_zero_of_real_mass_zero ρ hX hb hbound]
  · unfold maskedCircularSpectrum
    field_simp

theorem mass_mul_maskedCircularSpectrum_pair (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (r : ℝ) :
    (ρ₁.real X * ρ₂.real Y) *
        (maskedCircularSpectrum ρ₁ X b₁ r * maskedCircularSpectrum ρ₂ Y b₂ r) =
      r ^ 2 * maskedFourierPairCircleEnergy ρ₁ ρ₂ X Y b₁ b₂ r := by
  rw [maskedFourierPairCircleEnergy_eq]
  calc
    _ = (ρ₁.real X * maskedCircularSpectrum ρ₁ X b₁ r) *
        (ρ₂.real Y * maskedCircularSpectrum ρ₂ Y b₂ r) := by ring
    _ = _ := by
      rw [mass_mul_maskedCircularSpectrum ρ₁ X hb₁ hbound₁,
        mass_mul_maskedCircularSpectrum ρ₂ Y hb₂ hbound₂]
      ring

/-- The actual `F` is precisely the joint angular square integrated with the radial weight. -/
theorem mass_mul_maskedFourierEnergy (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (K v : ℕ) :
    (ρ₁.real X * ρ₂.real Y) * maskedFourierEnergy ρ₁ ρ₂ X Y b₁ b₂ K v =
      ((2 : ℝ) ^ v)⁻¹ * ∫ r in Ioi (0 : ℝ),
        maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) * r ^ 2 *
          maskedFourierPairCircleEnergy ρ₁ ρ₂ X Y b₁ b₂ r := by
  unfold maskedFourierEnergy dyadicFrequencyAverage
  rw [mul_left_comm, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with r
  rw [← mul_assoc, mul_comm (ρ₁.real X * ρ₂.real Y), mul_assoc,
    mass_mul_maskedCircularSpectrum_pair ρ₁ ρ₂ X Y hb₁ hb₂ hbound₁ hbound₂]
  ring

end FalconerThetaGauge
