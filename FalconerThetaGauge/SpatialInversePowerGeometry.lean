/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.SpatialInversePowerAtoms
public import FalconerThetaGauge.GaugeFrostmanDyadic

/-! # The literal normalized distance geometry of separated spatial balls -/

@[expose] public section

noncomputable section

open Finset Set Metric FalconerThetaGauge.GaugeFrostman

namespace FalconerThetaGauge

def spatialNormalizedCoordinate (center : Plane) (ρ : ℝ) (x : Plane) : Fin 2 → ℝ :=
  fun i ↦ (x i - center i) / ρ

def spatialSeparationCenterDirection (x₀ y₀ : Plane) : Fin 2 → ℝ :=
  fun i ↦ (x₀ i - y₀ i) / dist x₀ y₀

theorem abs_spatialNormalizedCoordinate_le_one {center x : Plane} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ closedBall center ρ) (i : Fin 2) :
    |spatialNormalizedCoordinate center ρ x i| ≤ 1 := by
  rw [spatialNormalizedCoordinate, abs_div, abs_of_pos hρ]
  apply (div_le_one hρ).mpr
  exact (abs_sub_coord_le_dist x center i).trans (mem_closedBall.mp hx)

theorem abs_spatialSeparationCenterDirection_le_one {x₀ y₀ : Plane}
    (hD : 0 < dist x₀ y₀) (i : Fin 2) :
    |spatialSeparationCenterDirection x₀ y₀ i| ≤ 1 := by
  rw [spatialSeparationCenterDirection, abs_div, abs_of_pos hD]
  exact (div_le_one hD).mpr (abs_sub_coord_le_dist x₀ y₀ i)

theorem spatialSeparationRatio_le {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ)
    (hsep : 50 * ρ ≤ dist x₀ y₀) : ρ / dist x₀ y₀ ≤ 1 / 50 := by
  have hD : 0 < dist x₀ y₀ := by linarith
  exact (div_le_iff₀ hD).mpr (by linarith)

theorem sum_spatialSeparationCoefficient_abs_le {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ)
    (hsep : 50 * ρ ≤ dist x₀ y₀) :
    (∑ k, |spatialSeparationAtomCoefficient (ρ / dist x₀ y₀)
      (spatialSeparationCenterDirection x₀ y₀) k|) ≤ 1 / 4 := by
  have hD : 0 < dist x₀ y₀ := by linarith
  exact sum_spatialSeparationAtomCoefficient_abs_le (by positivity)
    (spatialSeparationRatio_le hρ hsep) (abs_spatialSeparationCenterDirection_le_one hD)

theorem spatialDistancePerturbation_distance_identity {x₀ y₀ x y : Plane} {ρ : ℝ}
    (hρ : ρ ≠ 0) (hD : dist x₀ y₀ ≠ 0) :
    (dist x₀ y₀) ^ 2 * (1 + spatialDistancePerturbation (ρ / dist x₀ y₀)
      (spatialSeparationCenterDirection x₀ y₀)
      (spatialNormalizedCoordinate x₀ ρ x) (spatialNormalizedCoordinate y₀ ρ y)) =
        (dist x y) ^ 2 := by
  have hcenter : (dist x₀ y₀) ^ 2 = ∑ i, (x₀ i - y₀ i) ^ 2 := by
    rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
    rfl
  have hxy : (dist x y) ^ 2 = ∑ i, (x i - y i) ^ 2 := by
    rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
    rfl
  rw [hxy, spatialDistancePerturbation, mul_add, mul_one, mul_sum]
  conv_lhs => arg 1; rw [hcenter]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  simp only [spatialSeparationCenterDirection, spatialNormalizedCoordinate]
  field_simp
  ring

theorem spatialDistancePerturbation_eq_distance_ratio_sq {x₀ y₀ x y : Plane} {ρ : ℝ}
    (hρ : ρ ≠ 0) (hD : dist x₀ y₀ ≠ 0) :
    1 + spatialDistancePerturbation (ρ / dist x₀ y₀)
      (spatialSeparationCenterDirection x₀ y₀)
      (spatialNormalizedCoordinate x₀ ρ x) (spatialNormalizedCoordinate y₀ ρ y) =
        (dist x y / dist x₀ y₀) ^ 2 := by
  rw [div_pow]
  apply (eq_div_iff (pow_ne_zero 2 hD)).mpr
  simpa only [mul_comm] using spatialDistancePerturbation_distance_identity hρ hD

theorem spatialDistancePerturbation_inversePower_identity (j : ℕ)
    {x₀ y₀ x y : Plane} {ρ : ℝ} (hρ : ρ ≠ 0) (hD : 0 < dist x₀ y₀) :
    (dist x₀ y₀)⁻¹ ^ j *
      (1 + spatialDistancePerturbation (ρ / dist x₀ y₀)
        (spatialSeparationCenterDirection x₀ y₀)
        (spatialNormalizedCoordinate x₀ ρ x) (spatialNormalizedCoordinate y₀ ρ y)) ^
          (-(j : ℝ) / 2) = (dist x y)⁻¹ ^ j := by
  rw [spatialDistancePerturbation_eq_distance_ratio_sq hρ hD.ne',
    ← Real.rpow_natCast _ 2, ← Real.rpow_mul (div_nonneg dist_nonneg hD.le)]
  have he : (2 : ℝ) * (-(j : ℝ) / 2) = -(j : ℝ) := by ring
  simp only [Nat.cast_ofNat]
  rw [he, Real.rpow_neg_natCast, zpow_neg, zpow_natCast, div_pow, inv_div,
    inv_pow, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero j hD.ne'),
    one_mul, ← inv_pow]

end FalconerThetaGauge
