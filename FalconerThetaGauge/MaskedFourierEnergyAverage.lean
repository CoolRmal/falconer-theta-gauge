module

public import FalconerThetaGauge.MaskedFourierEnergy
public import FalconerThetaGauge.MaskedFourierEnergyCutoff

/-! # The literal dyadic Fourier energy and the trivial bound (7.1) -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter

namespace FalconerThetaGauge

/-- The actual energy `F_X,Y(v)` of Definition 7.1, allowing the two root measures. -/
def maskedFourierEnergy (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    (b₁ b₂ : Plane → UnitCircle → ℝ) (K v : ℕ) : ℝ :=
  dyadicFrequencyAverage K v
    (fun r ↦ maskedCircularSpectrum ρ₁ X b₁ r * maskedCircularSpectrum ρ₂ Y b₂ r)

theorem maskedFourierEnergy_nonneg (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    (b₁ b₂ : Plane → UnitCircle → ℝ) (K v : ℕ) :
    0 ≤ maskedFourierEnergy ρ₁ ρ₂ X Y b₁ b₂ K v :=
  dyadicFrequencyAverage_nonneg K v fun _r hr ↦
    mul_nonneg (maskedCircularSpectrum_nonneg ρ₁ X b₁ hr.le)
      (maskedCircularSpectrum_nonneg ρ₂ Y b₂ hr.le)

theorem maskedCircularSpectrum_mul_le (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) {r : ℝ} (hr : 0 ≤ r) :
    maskedCircularSpectrum ρ₁ X b₁ r * maskedCircularSpectrum ρ₂ Y b₂ r ≤
      (2 * Real.pi) ^ (2 : ℕ) * r ^ (2 : ℕ) * (ρ₁.real X * ρ₂.real Y) := by
  calc
    _ ≤ (2 * Real.pi * r * ρ₁.real X) * (2 * Real.pi * r * ρ₂.real Y) :=
      mul_le_mul (maskedCircularSpectrum_le ρ₁ X hb₁ hbound₁ hr)
        (maskedCircularSpectrum_le ρ₂ Y hb₂ hbound₂ hr)
        (maskedCircularSpectrum_nonneg ρ₂ Y b₂ hr) (by positivity)
    _ = _ := by ring

theorem integrable_maskedFourierEnergy_integrand (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (K v : ℕ) :
    Integrable (fun r ↦ maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) *
      (maskedCircularSpectrum ρ₁ X b₁ r * maskedCircularSpectrum ρ₂ Y b₂ r)) := by
  apply integrable_maskedFrequencyCutoff_mul K v
    ((measurable_maskedCircularSpectrum ρ₁ X hb₁).mul
      (measurable_maskedCircularSpectrum ρ₂ Y hb₂))
  intro r hr
  dsimp only [Pi.mul_apply]
  rw [abs_of_nonneg (mul_nonneg (maskedCircularSpectrum_nonneg ρ₁ X b₁ hr.1)
    (maskedCircularSpectrum_nonneg ρ₂ Y b₂ hr.1))]
  exact (maskedCircularSpectrum_mul_le ρ₁ ρ₂ X Y hb₁ hb₂ hbound₁ hbound₂ hr.1).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hr.1 hr.2 2) (sq_nonneg _)) (by positivity))

/-- The actual dyadic Fourier energy has the paper's constant 2600 and true carrier masses. -/
theorem maskedFourierEnergy_le (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (K v : ℕ) :
    maskedFourierEnergy ρ₁ ρ₂ X Y b₁ b₂ K v ≤
      2600 * (4 : ℝ) ^ v * (ρ₁.real X * ρ₂.real Y) := by
  let C := (2 * Real.pi) ^ (2 : ℕ) * (ρ₁.real X * ρ₂.real Y)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsq : ∀ r ∈ Icc 0 (4 * (2 : ℝ) ^ v), |r ^ (2 : ℕ)| ≤ (4 * (2 : ℝ) ^ v) ^ 2 := by
    intro r hr
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ hr.1 hr.2 2
  have hsqInt := integrable_maskedFrequencyCutoff_mul K v (measurable_id.pow_const 2) hsq
  have hmajor : Integrable (fun r ↦ maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) *
      (C * r ^ (2 : ℕ))) := by
    simpa only [id_eq, mul_assoc, mul_comm, mul_left_comm] using hsqInt.const_mul C
  have hpoint : ∀ r ∈ Ioi (0 : ℝ),
      maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) *
        (maskedCircularSpectrum ρ₁ X b₁ r * maskedCircularSpectrum ρ₂ Y b₂ r) ≤
      maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) * (C * r ^ (2 : ℕ)) := by
    intro r hr
    apply mul_le_mul_of_nonneg_left _ (maskedFrequencyCutoff_mem_Icc K _).1
    simpa only [C, mul_assoc, mul_comm, mul_left_comm] using
      maskedCircularSpectrum_mul_le ρ₁ ρ₂ X Y hb₁ hb₂ hbound₁ hbound₂ hr.le
  have hi := integrable_maskedFourierEnergy_integrand ρ₁ ρ₂ X Y hb₁ hb₂ hbound₁ hbound₂ K v
  calc
    _ ≤ dyadicFrequencyAverage K v (fun r ↦ C * r ^ (2 : ℕ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ ((2 : ℝ) ^ v)⁻¹)
      exact setIntegral_mono_on hi.integrableOn hmajor.integrableOn measurableSet_Ioi hpoint
    _ = C * dyadicFrequencyAverage K v (fun r ↦ r ^ (2 : ℕ)) := by
      unfold dyadicFrequencyAverage
      simp_rw [mul_left_comm (maskedFrequencyCutoff K _) C]
      rw [integral_const_mul]
      ring
    _ ≤ C * (64 * (4 : ℝ) ^ v) :=
      mul_le_mul_of_nonneg_left (dyadicFrequencyAverage_sq_le K v) hC
    _ ≤ _ := by
      have hπ : (2 * Real.pi) ^ (2 : ℕ) * 64 ≤ (2600 : ℝ) := by
        nlinarith [Real.pi_lt_d2, Real.pi_pos]
      have := mul_le_mul_of_nonneg_right hπ
        (show 0 ≤ (4 : ℝ) ^ v * (ρ₁.real X * ρ₂.real Y) by positivity)
      simpa only [C, mul_assoc, mul_comm, mul_left_comm] using this

end FalconerThetaGauge
