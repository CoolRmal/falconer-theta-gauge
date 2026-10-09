module

public import FalconerThetaGauge.MaskedDistanceEnergyFourier

/-! # Real frequency exponents in the actual distance collision energy -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function

namespace FalconerThetaGauge

/-- Actual collision energy at a real exponent, including the source's `t-εN`. -/
def normalizedDistanceCollisionEnergy (η : Measure ℝ) (m t : ℝ) : ℝ :=
  (2 : ℝ) ^ t / m * (scalarCollisionMass η η ((2 : ℝ) ^ (-t)) 0).toReal

/-- The real-exponent version of the literal weighted carrier energy. -/
def realMaskedDistanceEnergy (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    (Z : Set (Plane × Plane)) (t : ℝ) : ℝ :=
  normalizedDistanceCollisionEnergy (passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z)
    (ρ₁.real X * ρ₂.real Y) t

theorem realMaskedDistanceEnergy_nat (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    (Z : Set (Plane × Plane)) (t : ℕ) :
    realMaskedDistanceEnergy ρ₁ ρ₂ X Y Z (t : ℝ) = maskedDistanceEnergy ρ₁ ρ₂ X Y Z t := by
  simp only [realMaskedDistanceEnergy, normalizedDistanceCollisionEnergy,
    maskedDistanceEnergy, Real.rpow_natCast]

theorem normalizedDistanceCollisionEnergy_nonneg (η : Measure ℝ) {m : ℝ}
    (hm : 0 ≤ m) (t : ℝ) : 0 ≤ normalizedDistanceCollisionEnergy η m t := by
  exact mul_nonneg (div_nonneg (by positivity) hm) ENNReal.toReal_nonneg

theorem normalizedDistanceCollisionEnergy_mono {η ζ : Measure ℝ} [IsFiniteMeasure ζ]
    (hηζ : η ≤ ζ) {m : ℝ} (hm : 0 ≤ m) (t : ℝ) :
    normalizedDistanceCollisionEnergy η m t ≤ normalizedDistanceCollisionEnergy ζ m t := by
  let : IsFiniteMeasure η := isFiniteMeasure_of_le ζ hηζ
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by positivity) hm)
  apply ENNReal.toReal_mono (by unfold scalarCollisionMass; finiteness)
  exact Measure.le_iff.1 (Measure.prod_mono hηζ hηζ) _ (measurableSet_scalarCollision _ _)

/-- The normalized true collision energy is bounded by the actual angular Fourier window. -/
theorem normalizedDistanceCollisionEnergy_le_two_fourier (η : Measure ℝ) [IsFiniteMeasure η]
    {m : ℝ} (hm : 0 ≤ m) (t : ℝ) :
    normalizedDistanceCollisionEnergy η m t ≤
      2 / m * scalarFourierWindowIntegral η ((2 : ℝ) ^ t) := by
  have ht : 0 < (2 : ℝ) ^ t := by positivity
  have hinv : 1 / (2 : ℝ) ^ (-t) = (2 : ℝ) ^ t := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    simp
  have h := mul_le_mul_of_nonneg_left
    (scalarCollisionMass_toReal_le_two_mul_fourier η (by positivity : 0 < (2 : ℝ) ^ (-t)))
    (div_nonneg ht.le hm)
  rw [hinv] at h
  unfold normalizedDistanceCollisionEnergy
  convert h using 1
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp [ht.ne']

/-- The genuine low Fourier window is bounded by 320 times the actual collision energy. -/
theorem two_normalized_fourier_le_320_distance (η : Measure ℝ) [IsFiniteMeasure η]
    {m : ℝ} (hm : 0 ≤ m) (t : ℝ) :
    2 / m * scalarFourierWindowIntegral η ((2 : ℝ) ^ t) ≤
      320 * normalizedDistanceCollisionEnergy η m t := by
  have hinv : 1 / (2 : ℝ) ^ (-t) = (2 : ℝ) ^ t := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    simp
  have h := mul_le_mul_of_nonneg_left
    (scalarFourierWindowIntegral_le_160_collision η (by positivity : 0 < (2 : ℝ) ^ (-t)))
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hm)
  rw [hinv] at h
  convert h using 1
  unfold normalizedDistanceCollisionEnergy
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [div_eq_mul_inv, inv_inv]
  ring

end FalconerThetaGauge
