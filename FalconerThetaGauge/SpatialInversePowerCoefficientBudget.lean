/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.SpatialInversePowerSeparation
public import FalconerThetaGauge.SpatialInversePowerBinomialSharp

/-! # The literal square-root coefficient budget for separated inverse powers -/

@[expose] public section

noncomputable section

open Finset

namespace FalconerThetaGauge

theorem tsum_spatialSeparationWordCoefficient_abs_le_sqrt (j : ℕ) {D : ℝ} (hD : 0 < D)
    {a : SpatialSeparationAtom → ℝ} (ha : (∑ k, |a k|) ≤ 1 / 4) :
    (∑' w, |spatialSeparationWordCoefficient j D a w|) ≤ (Real.sqrt 2 / D) ^ j := by
  have hs := summable_spatialSeparationWordCoefficient_abs j hD ha
  rw [hs.tsum_sigma]
  simp_rw [tsum_fintype, sum_spatialSeparationWordCoefficient_abs j _ hD]
  rw [tsum_mul_left]
  calc
    _ ≤ D⁻¹ ^ j * (Real.sqrt 2) ^ j := mul_le_mul_of_nonneg_left
      (tsum_inversePowerBinomial_abs_le_sqrt j (sum_nonneg (fun _ _ ↦ abs_nonneg _)) ha)
      (by positivity)
    _ = _ := by rw [div_eq_mul_inv, mul_pow]; ring

theorem tsum_spatialInversePowerCoefficient_abs_le_sqrt (j : ℕ)
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀) :
    (∑' w, |spatialInversePowerCoefficient j x₀ y₀ ρ w|) ≤
      (Real.sqrt 2 / dist x₀ y₀) ^ j := by
  have hD : 0 < dist x₀ y₀ := by linarith
  exact tsum_spatialSeparationWordCoefficient_abs_le_sqrt j hD
    (sum_spatialSeparationCoefficient_abs_le hρ hsep)

end FalconerThetaGauge
