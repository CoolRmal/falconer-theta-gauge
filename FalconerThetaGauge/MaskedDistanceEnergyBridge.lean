module

public import FalconerThetaGauge.MaskedDistanceEnergyLevelMeasures

/-! # Source Lemma 7.4 for the actual scheduled passing and masked distance measures -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- The genuine scheduled low/high bridge: all measure comparisons follow from
the literal convolution masks and actual L2, and both Fourier bounds are proved. -/
theorem scheduledDistanceEnergy_low_high (ρ₁ ρ₂ : Measure Plane)
    [IsProbabilityMeasure ρ₁] [IsProbabilityMeasure ρ₂]
    (hρ₁ : ρ₁ unitSquare = 1) (hρ₂ : ρ₂ unitSquare = 1) {X Y : Set Plane}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ x ∈ X, ∀ y ∈ Y, d ≤ dist x y) (E : ℝ)
    {L : ℕ} (hL : 0 < L) (hsize : (L : ℝ) ≤ (2 : ℝ) ^ E / 8)
    (i K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest)
    (hordered₁ : ScheduledTestsOrdered I₁) (hordered₂ : ScheduledTestsOrdered I₂)
    {s : ℝ} (hs : 0 ≤ s) (t : ℕ) (hst : s ≤ (t : ℝ)) :
    scheduledDistanceEnergy ρ₁ ρ₂ X Y E (directionalLevelWidth L i) I₁ I₂ t ≤
      320 * realMaskedDistanceEnergy ρ₁ ρ₂ X Y
        (scheduledPassingPairSet ρ₁ ρ₂ E (directionalLevelWidth L (i + 1)) I₁ I₂) s +
      320 / (ρ₁.real X * ρ₂.real Y) *
        ∑ v ∈ scalarHighDyadicIndices s t,
          scalarDyadicFourierShellIntegral
            (levelMaskedDistanceMeasure ρ₁ ρ₂ X Y E L i K I₁ I₂) v := by
  let : IsFiniteMeasure (passingWeightedDistanceMeasure ρ₁ ρ₂ X Y
      (scheduledPassingPairSet ρ₁ ρ₂ E (directionalLevelWidth L (i + 1)) I₁ I₂)) :=
    isFiniteMeasure_passingWeightedDistanceMeasure ρ₁ ρ₂ hX hY _
      (fun x hx y hy ↦ crossDistanceWeight_le_of_dist hd (hsep x hx y hy))
  have h := normalizedDistanceCollisionEnergy_le_320_low_high_dyadic
    (passingWeightedDistanceMeasure_le_levelMasked ρ₁ ρ₂ hρ₁ hρ₂ X Y E L i K I₁ I₂)
    (levelMaskedDistanceMeasure_le_nextPassing ρ₁ ρ₂ hρ₁ hρ₂ X Y E hL hsize i K I₁ I₂
      hordered₁ hordered₂) (by positivity : 0 ≤ ρ₁.real X * ρ₂.real Y) hs t hst
  simpa only [scheduledDistanceEnergy, realMaskedDistanceEnergy, normalizedDistanceCollisionEnergy,
    maskedDistanceEnergy, Real.rpow_natCast] using h

/-- Literal Lemma 7.4 at `s=t-εN`, with the source's separated cells, actual level
products, next-level passing measure, finite dyadic sum, and constant `C₁=320`. -/
theorem scheduledDistanceEnergy_cells_low_high (ρ₁ ρ₂ : Measure Plane)
    [IsProbabilityMeasure ρ₁] [IsProbabilityMeasure ρ₂]
    (hρ₁ : ρ₁ unitSquare = 1) (hρ₂ : ρ₂ unitSquare = 1) {a : ℕ} {P Q : Fin 2 → ℤ}
    (hsep : SeparatedDyadicCells a P Q) {E : ℝ} (hE : 0 ≤ E)
    {L : ℕ} (hL : 0 < L) (hsize : (L : ℝ) ≤ (2 : ℝ) ^ E / 8)
    (i K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest)
    (hordered₁ : ScheduledTestsOrdered I₁) (hordered₂ : ScheduledTestsOrdered I₂)
    (t : ℕ) (hfreq : (a : ℝ) < (t : ℝ) - E) :
    scheduledDistanceEnergy ρ₁ ρ₂ (dyadicCube a P) (dyadicCube a Q) E
        (directionalLevelWidth L i) I₁ I₂ t ≤
      320 * realMaskedDistanceEnergy ρ₁ ρ₂ (dyadicCube a P) (dyadicCube a Q)
        (scheduledPassingPairSet ρ₁ ρ₂ E (directionalLevelWidth L (i + 1)) I₁ I₂) ((t : ℝ) - E) +
      320 / (ρ₁.real (dyadicCube a P) * ρ₂.real (dyadicCube a Q)) *
        ∑ v ∈ scalarHighDyadicIndices ((t : ℝ) - E) t,
          scalarDyadicFourierShellIntegral
            (levelMaskedDistanceMeasure ρ₁ ρ₂ (dyadicCube a P) (dyadicCube a Q)
              E L i K I₁ I₂) v := by
  exact scheduledDistanceEnergy_low_high ρ₁ ρ₂ hρ₁ hρ₂
    (measurableSet_dyadicCube a P) (measurableSet_dyadicCube a Q)
    (mul_pos (by norm_num : (0 : ℝ) < 500) (dyadicRadius_pos a))
    (fun _x hx _y hy ↦ (dist_bounds_of_separatedDyadicCells hsep hx hy).1)
    E hL hsize i K I₁ I₂ hordered₁ hordered₂
    (by have := Nat.cast_nonneg (α := ℝ) a; linarith) t (by linarith)

end FalconerThetaGauge
