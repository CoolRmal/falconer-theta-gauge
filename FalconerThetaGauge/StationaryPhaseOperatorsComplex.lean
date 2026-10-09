/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.StationaryPhaseOperators

/-!
# The two constant-coefficient stationary-phase operators
-/

@[expose] public section

noncomputable section

open Finset
open scoped ContDiff

namespace FalconerThetaGauge

/-- The source's positive-sign operator coefficient. -/
def stationaryPhaseCoefficient (j k : ℕ) : ℂ :=
  (Complex.I / 2) ^ j / (j.factorial : ℂ) * (stationaryDerivativeCoefficient (2 * j) k : ℂ)

/-- The operator at the opposite stationary point has conjugate coefficients. -/
def stationaryPhaseConjugateCoefficient (j k : ℕ) : ℂ :=
  star (stationaryPhaseCoefficient j k)

def stationaryPhaseOperator (j : ℕ) (G : ℝ → ℂ) (φ : ℝ) : ℂ :=
  ∑ k ∈ range (2 * j + 1), stationaryPhaseCoefficient j k * iteratedDeriv k G φ

def stationaryPhaseConjugateOperator (j : ℕ) (G : ℝ → ℂ) (φ : ℝ) : ℂ :=
  ∑ k ∈ range (2 * j + 1), stationaryPhaseConjugateCoefficient j k * iteratedDeriv k G φ

theorem stationaryPhaseCoefficient_zero : stationaryPhaseCoefficient 0 0 = 1 := by
  simp [stationaryPhaseCoefficient, stationaryDerivativeCoefficient_zero]

theorem stationaryPhaseCoefficient_eq_zero {j k : ℕ} (hk : 2 * j < k) :
    stationaryPhaseCoefficient j k = 0 := by
  rw [stationaryPhaseCoefficient, stationaryDerivativeCoefficient_eq_zero hk]
  simp

theorem stationaryPhaseConjugateCoefficient_eq (j k : ℕ) :
    stationaryPhaseConjugateCoefficient j k =
      (-Complex.I / 2) ^ j / (j.factorial : ℂ) *
        (stationaryDerivativeCoefficient (2 * j) k : ℂ) := by
  simp [stationaryPhaseConjugateCoefficient, stationaryPhaseCoefficient]

theorem norm_stationaryPhaseConjugateCoefficient (j k : ℕ) :
    ‖stationaryPhaseConjugateCoefficient j k‖ = ‖stationaryPhaseCoefficient j k‖ := by
  simp [stationaryPhaseConjugateCoefficient]

theorem stationaryPhaseOperator_zero (G : ℝ → ℂ) (φ : ℝ) :
    stationaryPhaseOperator 0 G φ = G φ := by
  simp [stationaryPhaseOperator, stationaryPhaseCoefficient_zero]

theorem stationaryPhaseConjugateOperator_zero (G : ℝ → ℂ) (φ : ℝ) :
    stationaryPhaseConjugateOperator 0 G φ = G φ := by
  simp [stationaryPhaseConjugateOperator, stationaryPhaseConjugateCoefficient,
    stationaryPhaseCoefficient_zero]

/-- Exact positive-sign operator applied to the literal weighted Morse amplitude. -/
theorem stationaryPhaseOperator_eq_scaled_derivative
    {G : ℝ → ℂ} {φ : ℝ} {j : ℕ} (hG : ContDiffAt ℝ (2 * j) G φ) :
    stationaryPhaseOperator j G φ = (Complex.I / 2) ^ j / (j.factorial : ℂ) *
      iteratedDeriv (2 * j)
        (fun s => G (φ + stationaryMorseAngle s) * stationaryMorseJacobian s) 0 := by
  rw [iteratedDeriv_stationaryMorse_weighted hG, mul_sum]
  apply sum_congr rfl
  intro k _
  simp only [stationaryPhaseCoefficient]
  ring

/-- Exact negative-sign operator applied to the same weighted Morse amplitude. -/
theorem stationaryPhaseConjugateOperator_eq_scaled_derivative
    {G : ℝ → ℂ} {φ : ℝ} {j : ℕ} (hG : ContDiffAt ℝ (2 * j) G φ) :
    stationaryPhaseConjugateOperator j G φ = (-Complex.I / 2) ^ j / (j.factorial : ℂ) *
      iteratedDeriv (2 * j)
        (fun s => G (φ + stationaryMorseAngle s) * stationaryMorseJacobian s) 0 := by
  rw [iteratedDeriv_stationaryMorse_weighted hG, mul_sum]
  apply sum_congr rfl
  intro k _
  rw [stationaryPhaseConjugateCoefficient_eq]
  ring

end FalconerThetaGauge
