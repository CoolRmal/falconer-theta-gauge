module

public import FalconerThetaGauge.DirectionalTestsAverageGrid

/-!
# Actual normalized-anchor ball mass

The exact nine-square cover and the genuine regularity estimate control every
closed ball for the normalized restriction to an occupied anchor.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- The actual anchor restriction's real mass is bounded by the original mass divided
by the actual positive anchor mass. -/
theorem real_projectionAnchorMeasure_le_div (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (p : ℕ) (P : Fin 2 → ℤ) (hP : 0 < unitCellWeight ρ p P)
    {A : Set Plane} (hA : MeasurableSet A) :
    (projectionAnchorMeasure ρ p P).real A ≤ ρ.real A / unitCellWeight ρ p P := by
  rw [projectionAnchorMeasure, Measure.real, normalizedRestrict_apply ρ _ _ hA,
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  change (unitCellWeight ρ p P)⁻¹ * ρ.real (A ∩ dyadicCube p P) ≤ _
  rw [div_eq_mul_inv, mul_comm (ρ.real A)]
  exact mul_le_mul_of_nonneg_left (measureReal_mono inter_subset_left) (inv_nonneg.2 hP.le)

/-- Genuine regularity compares the maximal anchor mass with any occupied anchor. -/
theorem maxCellMass_le_regularity_mul_anchor (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    {ε : ℝ} {N p : ℕ} (hreg : IsRegularThrough ε N ρ) (hp : p ≤ N)
    (P : Fin 2 → ℤ) (hP : 0 < unitCellWeight ρ p P) :
    maxCellMass ρ p ≤ (2 : ℝ) ^ (ε * N) * unitCellWeight ρ p P := by
  obtain ⟨k, _, hmax⟩ := exists_unitCellWeight_eq_maxCellMass ρ p
  rw [hmax]
  exact hreg p hp k P hP

/-- The actual normalized anchor probability obeys the nine-cell ball estimate. -/
theorem real_projectionAnchor_closedBall_le_nine_ratio (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {ε : ℝ} {N p : ℕ}
    (hreg : IsRegularThrough ε N ρ) (hp : p ≤ N) (P : Fin 2 → ℤ)
    (hP : 0 < unitCellWeight ρ p P) (d : ℕ) (z : Plane) :
    (projectionAnchorMeasure ρ p P).real (Metric.closedBall z (dyadicRadius d)) ≤
      9 * (2 : ℝ) ^ (ε * N) * (maxCellMass ρ d / maxCellMass ρ p) := by
  have hmass := real_projectionAnchorMeasure_le_div ρ p P hP
    (A := Metric.closedBall z (dyadicRadius d)) Metric.isClosed_closedBall.measurableSet
  have hball := real_closedBall_dyadicRadius_le_nine_maxCellMass ρ hρ d z
  have hmax := maxCellMass_le_regularity_mul_anchor ρ hreg hp P hP
  have hMp := maxCellMass_pos ρ hρ p
  calc
    _ ≤ 9 * maxCellMass ρ d / unitCellWeight ρ p P := hmass.trans
      (div_le_div_of_nonneg_right hball hP.le)
    _ ≤ _ := by
      apply (div_le_iff₀ hP).2
      have hmul := mul_le_mul_of_nonneg_left hmax
        (show 0 ≤ 9 * maxCellMass ρ d / maxCellMass ρ p from
          div_nonneg (mul_nonneg (by norm_num) (maxCellMass_nonneg ρ d)) hMp.le)
      rw [div_mul_cancel₀ _ hMp.ne'] at hmul
      convert hmul using 1
      ring

/-- The literal actual-maximal-mass ratio in terms of the source excess function. -/
theorem maxCellMass_ratio_eq_excess (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {N : ℕ} (hN : 0 < N) (d p : ℕ) :
    maxCellMass ρ d / maxCellMass ρ p =
      (2 : ℝ) ^ (-((d : ℝ) - p)) *
        (2 : ℝ) ^ ((N : ℝ) * (regularMeasureExcess ρ N p - regularMeasureExcess ρ N d)) := by
  rw [maxCellMass_eq_power_excess ρ hρ hN d, maxCellMass_eq_power_excess ρ hρ hN p]
  simp only [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- The normalized anchor's genuine ball estimate in the manuscript's excess notation. -/
theorem real_projectionAnchor_closedBall_le_excess (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {ε : ℝ} {N p : ℕ} (hN : 0 < N)
    (hreg : IsRegularThrough ε N ρ) (hp : p ≤ N) (P : Fin 2 → ℤ)
    (hP : 0 < unitCellWeight ρ p P) (d : ℕ) (z : Plane) :
    (projectionAnchorMeasure ρ p P).real (Metric.closedBall z (dyadicRadius d)) ≤
      9 * (2 : ℝ) ^ (ε * N) * (2 : ℝ) ^ (-((d : ℝ) - p)) *
        (2 : ℝ) ^ ((N : ℝ) * (regularMeasureExcess ρ N p - regularMeasureExcess ρ N d)) := by
  have h := real_projectionAnchor_closedBall_le_nine_ratio ρ hρ hreg hp P hP d z
  rw [maxCellMass_ratio_eq_excess ρ hρ hN d p, ← mul_assoc] at h
  exact h

end FalconerThetaGauge
