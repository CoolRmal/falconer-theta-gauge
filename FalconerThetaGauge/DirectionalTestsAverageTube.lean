module

public import FalconerThetaGauge.DirectionalTestsAverageTubeShells
public import FalconerThetaGauge.DirectionalTestsAverageGridTotal

/-! # Actual tube averages and their genuine finite occupied-center shell reduction -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman

/-- Precisely the occupied centers admitted by the true radial truncation of the tube. -/
def occupiedTubeRadiusCenters (ρ : Measure Plane) (g p : ℕ) (P : Fin 2 → ℤ) :
    Finset (Fin 2 → ℤ) :=
  (occupiedUnitCells ρ p).filter (fun Q ↦
    ‖dyadicCellCenter p Q - dyadicCellCenter p P‖ ≤ 4 * (2 : ℝ) ^ (-(g : ℝ)))

theorem tubeCount_eq_sum_lineBands (ρ : Measure Plane) (g p : ℕ) (E width : ℝ)
    (P : Fin 2 → ℤ) (w : UnitCircle) :
    tubeCount ρ g p E width P w =
      ∑ Q ∈ occupiedTubeRadiusCenters ρ g p P,
        (lineDistanceDirectionBand (dyadicCellCenter p P) (dyadicCellCenter p Q)
          (width * (2 : ℝ) ^ (-(p : ℝ)) * (2 : ℝ) ^ (2 * E))).indicator (fun _ ↦ (1 : ℝ)) w := by
  rw [occupiedTubeRadiusCenters, Finset.sum_filter]
  unfold tubeCount
  apply Finset.sum_congr rfl
  intro Q _
  by_cases hQ : ‖dyadicCellCenter p Q - dyadicCellCenter p P‖ ≤ 4 * (2 : ℝ) ^ (-(g : ℝ))
  · simp only [indicator, directionalTube, lineDistanceDirectionBand, mem_ofPred_eq,
      hQ, and_true, ite_true]
    rfl
  · simp only [indicator, directionalTube, lineDistanceDirectionBand, mem_ofPred_eq,
      hQ, and_false, ite_false]

theorem circleArcLength_lineDistanceDirectionBand_le_majorant (c z : Plane) {η : ℝ}
    (hη : 0 ≤ η) :
    circleArcLength (lineDistanceDirectionBand c z η) ≤
      ENNReal.ofReal (2 * Real.pi * angularCollisionMajorant η (z - c)) := by
  by_cases hz : z = c
  · simp only [hz, sub_self, angularCollisionMajorant, ite_true, mul_one]
    calc
      _ ≤ circleArcLength univ := measure_mono (subset_univ _)
      _ = _ := circleArcLength_univ
  · simpa only [angularCollisionMajorant, ite_eq_right (sub_ne_zero.mpr hz)] using
      circleArcLength_lineDistanceDirectionBand_le c z hz hη

/-- The true tube average is bounded by the actual finite sum of capped inverse center distances. -/
theorem tubeAverage_le_sum_collision (ρ : Measure Plane) (g p : ℕ) (E : ℝ) (P : Fin 2 → ℤ) :
    tubeAverage ρ g p E P ≤ ∑ Q ∈ occupiedTubeRadiusCenters ρ g p P,
      angularCollisionMajorant (2 * (2 : ℝ) ^ (-(p : ℝ)) * (2 : ℝ) ^ (2 * E))
        (dyadicCellCenter p Q - dyadicCellCenter p P) := by
  let η : ℝ := 2 * (2 : ℝ) ^ (-(p : ℝ)) * (2 : ℝ) ^ (2 * E)
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have heq : tubeCount ρ g p E 2 P = fun w ↦
      ∑ Q ∈ occupiedTubeRadiusCenters ρ g p P,
        (lineDistanceDirectionBand (dyadicCellCenter p P) (dyadicCellCenter p Q) η).indicator
          (fun _ ↦ (1 : ℝ)) w := funext (tubeCount_eq_sum_lineBands ρ g p E 2 P)
  have hsum : (∑ Q ∈ occupiedTubeRadiusCenters ρ g p P,
      circleArcLength.real (lineDistanceDirectionBand (dyadicCellCenter p P)
        (dyadicCellCenter p Q) η)) ≤
      (2 * Real.pi) * (∑ Q ∈ occupiedTubeRadiusCenters ρ g p P,
        angularCollisionMajorant η (dyadicCellCenter p Q - dyadicCellCenter p P)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro Q _
    exact ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg (by positivity) (angularCollisionMajorant_mem_Icc hη _).1)
      (circleArcLength_lineDistanceDirectionBand_le_majorant _ _ hη)
  unfold tubeAverage directionalAverage
  rw [heq, integral_finsetSum _ (fun Q _ ↦ (integrable_const (1 : ℝ)).indicator
    (measurableSet_lineDistanceDirectionBand _ _ _))]
  simp only [integral_indicator_const _ (measurableSet_lineDistanceDirectionBand _ _ _),
    smul_eq_mul, mul_one]
  have h := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ (2 * Real.pi)⁻¹)
  simpa only [← mul_assoc, inv_mul_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_mul] using h

/-- Actual shell-center subsets of the radial tube truncation are bounded by
all occupied centers in the same genuine dyadic disc. -/
theorem occupiedTubeRadiusCenters_ball_count_le (ρ : Measure Plane) (g p d : ℕ)
    (P : Fin 2 → ℤ) :
    (((occupiedTubeRadiusCenters ρ g p P).filter (fun Q ↦
      ‖dyadicCellCenter p Q - dyadicCellCenter p P‖ ≤ dyadicRadius d)).card : ℝ) ≤
      ((occupiedCellCentersInBall ρ p d (dyadicCellCenter p P)).card : ℝ) := by
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro Q hQ
  obtain ⟨hQrad, hQball⟩ := Finset.mem_filter.mp hQ
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hQrad).1,
    (Metric.mem_closedBall.mpr (by simpa only [dist_eq_norm] using hQball))⟩

/-- The exact source radius is the outer shell radius after discarding two generations. -/
theorem four_dyadicRadius_eq_sub_two {g : ℕ} (hg : 2 ≤ g) :
    4 * (2 : ℝ) ^ (-(g : ℝ)) = dyadicRadius (g - 2) := by
  rw [dyadicRadius, Nat.cast_sub hg]
  have h : (2 : ℝ) ^ (2 : ℝ) * (2 : ℝ) ^ (-(g : ℝ)) =
      (2 : ℝ) ^ (-((g : ℝ) - 2)) := by
    rw [← Real.rpow_add (by norm_num)]
    congr 1
    ring
  rw [show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num] at h
  norm_num only [Nat.cast_ofNat]
  exact h

end FalconerThetaGauge
