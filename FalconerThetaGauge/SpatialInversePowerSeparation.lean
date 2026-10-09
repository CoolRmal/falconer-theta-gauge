/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.SpatialInversePowerGeometry
public import Mathlib.Algebra.MvPolynomial.Monad

/-! # Actual uniformly convergent separated inverse-distance polynomial series -/

@[expose] public section

noncomputable section

open Finset Set Metric

namespace FalconerThetaGauge

def spatialNormalizedCoordinatePolynomial (center : Plane) (ρ : ℝ) (i : Fin 2) :
    MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.C ρ⁻¹ * (MvPolynomial.X i - MvPolynomial.C (center i))

theorem eval_spatialNormalizedCoordinatePolynomial (center x : Plane) (ρ : ℝ)
    (i : Fin 2) :
    MvPolynomial.eval (fun k ↦ x k) (spatialNormalizedCoordinatePolynomial center ρ i) =
      spatialNormalizedCoordinate center ρ x i := by
  simp [spatialNormalizedCoordinatePolynomial, spatialNormalizedCoordinate, div_eq_mul_inv,
    mul_comm]

def spatialSeparationLeftPolynomial (center : Plane) (ρ : ℝ)
    (w : SpatialSeparationWord) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.bind₁ (spatialNormalizedCoordinatePolynomial center ρ)
    (spatialSeparationWordLeftPolynomial w)

def spatialSeparationRightPolynomial (center : Plane) (ρ : ℝ)
    (w : SpatialSeparationWord) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.bind₁ (spatialNormalizedCoordinatePolynomial center ρ)
    (spatialSeparationWordRightPolynomial w)

theorem eval_spatialSeparationLeftPolynomial (center x : Plane) (ρ : ℝ)
    (w : SpatialSeparationWord) :
    MvPolynomial.eval (fun i ↦ x i) (spatialSeparationLeftPolynomial center ρ w) =
      ∏ r, spatialSeparationAtomLeft (spatialNormalizedCoordinate center ρ x) (w.2 r) := by
  rw [spatialSeparationLeftPolynomial]
  simp only [MvPolynomial.eval, MvPolynomial.eval₂Hom_bind₁]
  change MvPolynomial.eval
    (fun i ↦ MvPolynomial.eval (fun k ↦ x k)
      (spatialNormalizedCoordinatePolynomial center ρ i)) _ = _
  simp_rw [eval_spatialNormalizedCoordinatePolynomial]
  exact eval_spatialSeparationWordLeftPolynomial _ _

theorem eval_spatialSeparationRightPolynomial (center x : Plane) (ρ : ℝ)
    (w : SpatialSeparationWord) :
    MvPolynomial.eval (fun i ↦ x i) (spatialSeparationRightPolynomial center ρ w) =
      ∏ r, spatialSeparationAtomRight (spatialNormalizedCoordinate center ρ x) (w.2 r) := by
  rw [spatialSeparationRightPolynomial]
  simp only [MvPolynomial.eval, MvPolynomial.eval₂Hom_bind₁]
  change MvPolynomial.eval
    (fun i ↦ MvPolynomial.eval (fun k ↦ x k)
      (spatialNormalizedCoordinatePolynomial center ρ i)) _ = _
  simp_rw [eval_spatialNormalizedCoordinatePolynomial]
  exact eval_spatialSeparationWordRightPolynomial _ _

theorem abs_eval_spatialSeparationLeftPolynomial_le_one {center x : Plane} {ρ : ℝ}
    (hρ : 0 < ρ) (hx : x ∈ closedBall center ρ) (w : SpatialSeparationWord) :
    |MvPolynomial.eval (fun i ↦ x i) (spatialSeparationLeftPolynomial center ρ w)| ≤ 1 := by
  rw [eval_spatialSeparationLeftPolynomial, ← eval_spatialSeparationWordLeftPolynomial]
  exact abs_eval_spatialSeparationWordLeftPolynomial_le_one
    (abs_spatialNormalizedCoordinate_le_one hρ hx) w

theorem abs_eval_spatialSeparationRightPolynomial_le_one {center x : Plane} {ρ : ℝ}
    (hρ : 0 < ρ) (hx : x ∈ closedBall center ρ) (w : SpatialSeparationWord) :
    |MvPolynomial.eval (fun i ↦ x i) (spatialSeparationRightPolynomial center ρ w)| ≤ 1 := by
  rw [eval_spatialSeparationRightPolynomial, ← eval_spatialSeparationWordRightPolynomial]
  exact abs_eval_spatialSeparationWordRightPolynomial_le_one
    (abs_spatialNormalizedCoordinate_le_one hρ hx) w

def spatialInversePowerCoefficient (j : ℕ) (x₀ y₀ : Plane) (ρ : ℝ)
    (w : SpatialSeparationWord) : ℝ :=
  spatialSeparationWordCoefficient j (dist x₀ y₀)
    (spatialSeparationAtomCoefficient (ρ / dist x₀ y₀)
      (spatialSeparationCenterDirection x₀ y₀)) w

def spatialInversePowerTerm (j : ℕ) (x₀ y₀ : Plane) (ρ : ℝ)
    (w : SpatialSeparationWord) (p : Plane × Plane) : ℝ :=
  spatialInversePowerCoefficient j x₀ y₀ ρ w *
    MvPolynomial.eval (fun i ↦ p.1 i) (spatialSeparationLeftPolynomial x₀ ρ w) *
    MvPolynomial.eval (fun i ↦ p.2 i) (spatialSeparationRightPolynomial y₀ ρ w)

theorem spatialInversePowerTerm_eq_wordTerm (j : ℕ) (x₀ y₀ : Plane) (ρ : ℝ)
    (w : SpatialSeparationWord) (p : Plane × Plane) :
    spatialInversePowerTerm j x₀ y₀ ρ w p = spatialSeparationWordTerm j (dist x₀ y₀)
      (spatialSeparationAtomCoefficient (ρ / dist x₀ y₀)
        (spatialSeparationCenterDirection x₀ y₀))
      (spatialSeparationAtomLeft (spatialNormalizedCoordinate x₀ ρ p.1))
      (spatialSeparationAtomRight (spatialNormalizedCoordinate y₀ ρ p.2)) w := by
  simp only [spatialInversePowerTerm, spatialInversePowerCoefficient,
    eval_spatialSeparationLeftPolynomial, eval_spatialSeparationRightPolynomial,
    spatialSeparationWordTerm]

theorem summable_spatialInversePowerCoefficient_abs (j : ℕ) {x₀ y₀ : Plane} {ρ : ℝ}
    (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀) :
    Summable (fun w ↦ |spatialInversePowerCoefficient j x₀ y₀ ρ w|) := by
  have hD : 0 < dist x₀ y₀ := by linarith
  exact summable_spatialSeparationWordCoefficient_abs j hD
    (sum_spatialSeparationCoefficient_abs_le hρ hsep)

theorem tsum_spatialInversePowerCoefficient_abs_le (j : ℕ) {x₀ y₀ : Plane} {ρ : ℝ}
    (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀) :
    (∑' w, |spatialInversePowerCoefficient j x₀ y₀ ρ w|) ≤
      2 * (2 / dist x₀ y₀) ^ j := by
  have hD : 0 < dist x₀ y₀ := by linarith
  exact tsum_spatialSeparationWordCoefficient_abs_le j hD
    (sum_spatialSeparationCoefficient_abs_le hρ hsep)

theorem norm_spatialInversePowerTerm_le (j : ℕ) {x₀ y₀ : Plane} {ρ : ℝ}
    (hρ : 0 < ρ) (w : SpatialSeparationWord) {p : Plane × Plane}
    (hp : p ∈ closedBall x₀ ρ ×ˢ closedBall y₀ ρ) :
    ‖spatialInversePowerTerm j x₀ y₀ ρ w p‖ ≤
      |spatialInversePowerCoefficient j x₀ y₀ ρ w| := by
  rw [spatialInversePowerTerm_eq_wordTerm]
  exact norm_spatialSeparationWordTerm_le j _ _ _ _
    (abs_spatialSeparationAtomLeft_le_one
      (abs_spatialNormalizedCoordinate_le_one hρ hp.1))
    (abs_spatialSeparationAtomRight_le_one
      (abs_spatialNormalizedCoordinate_le_one hρ hp.2)) w

theorem hasSum_spatialInversePowerTerm (j : ℕ) {x₀ y₀ x y : Plane} {ρ : ℝ}
    (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    (hx : x ∈ closedBall x₀ ρ) (hy : y ∈ closedBall y₀ ρ) :
    HasSum (fun w ↦ spatialInversePowerTerm j x₀ y₀ ρ w (x, y))
      ((dist x y)⁻¹ ^ j) := by
  have hD : 0 < dist x₀ y₀ := by linarith
  have hs := hasSum_spatialSeparationWordTerm j hD
    (sum_spatialSeparationCoefficient_abs_le hρ hsep)
    (spatialSeparationAtomLeft (spatialNormalizedCoordinate x₀ ρ x))
    (spatialSeparationAtomRight (spatialNormalizedCoordinate y₀ ρ y))
    (abs_spatialSeparationAtomLeft_le_one (abs_spatialNormalizedCoordinate_le_one hρ hx))
    (abs_spatialSeparationAtomRight_le_one (abs_spatialNormalizedCoordinate_le_one hρ hy))
  rw [← spatialDistancePerturbation_eq_separated_sum,
    spatialDistancePerturbation_inversePower_identity j hρ.ne' hD] at hs
  simpa only [spatialInversePowerTerm_eq_wordTerm] using hs

theorem hasSumUniformlyOn_spatialInversePowerTerm (j : ℕ) {x₀ y₀ : Plane} {ρ : ℝ}
    (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀) :
    HasSumUniformlyOn (spatialInversePowerTerm j x₀ y₀ ρ)
      (fun p : Plane × Plane ↦ (dist p.1 p.2)⁻¹ ^ j)
      (closedBall x₀ ρ ×ˢ closedBall y₀ ρ) := by
  have hu := HasSumUniformlyOn.of_norm_le_summable
    (summable_spatialInversePowerCoefficient_abs j hρ hsep)
    (norm_spatialInversePowerTerm_le j hρ)
  apply hu.congr_right
  intro p hp
  exact (hasSum_spatialInversePowerTerm j hρ hsep hp.1 hp.2).tsum_eq

end FalconerThetaGauge
