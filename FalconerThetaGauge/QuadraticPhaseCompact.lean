module

public import FalconerThetaGauge.QuadraticPhaseExpansion
public import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Quadratic stationary phase for smooth compact amplitudes in both signs

The compact amplitudes used by the circle localization are genuine Schwartz
maps. Conjugation gives the second stationary point without a second
Fourier or Gaussian assumption.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset
open scoped ContDiff ComplexConjugate

namespace FalconerThetaGauge

theorem iteratedDeriv_conj (n : ℕ) (g : ℝ → ℂ) (x : ℝ) :
    iteratedDeriv n (fun t ↦ conj (g t)) x = conj (iteratedDeriv n g x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, show iteratedDeriv n (fun t ↦ conj (g t)) =
      fun t ↦ conj (iteratedDeriv n g t) from funext ih, iteratedDeriv_succ]
    exact deriv.star

/-- The positive quadratic expansion for the actual compact circle amplitude. -/
theorem quadratic_phase_compact {Λ : ℝ} (hΛ : 0 < Λ) (T : ℕ)
    {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g) :
    ‖(∫ s : ℝ, Complex.exp (((Λ / 2 * s ^ 2 : ℝ) : ℂ) * Complex.I) * g s) -
      (Real.sqrt (2 * Real.pi / Λ) : ℂ) *
        Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
          ∑ j ∈ range T, quadraticTaylorCoefficient Λ j * iteratedDeriv (2 * j) g 0‖ ≤
      Real.sqrt (2 / Λ) * (2 * Λ)⁻¹ ^ T / (T.factorial : ℝ) *
        ((∫ x : ℝ, ‖iteratedDeriv (2 * T) g x‖) +
          (∫ x : ℝ, ‖iteratedDeriv (2 * T + 2) g x‖)) :=
  quadratic_phase_expansion hΛ T (hs.toSchwartzMap hg)

/-- The conjugate expansion for the negative quadratic phase. -/
theorem quadratic_phase_compact_negative {Λ : ℝ} (hΛ : 0 < Λ) (T : ℕ)
    {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g) :
    ‖(∫ s : ℝ, Complex.exp (-((Λ / 2 * s ^ 2 : ℝ) : ℂ) * Complex.I) * g s) -
      conj (quadraticPhasePrefactor Λ) *
        ∑ j ∈ range T, conj (quadraticTaylorCoefficient Λ j) * iteratedDeriv (2 * j) g 0‖ ≤
      Real.sqrt (2 / Λ) * (2 * Λ)⁻¹ ^ T / (T.factorial : ℝ) *
        ((∫ x : ℝ, ‖iteratedDeriv (2 * T) g x‖) +
          (∫ x : ℝ, ‖iteratedDeriv (2 * T + 2) g x‖)) := by
  have hgconj : ContDiff ℝ ∞ (fun t ↦ conj (g t)) :=
    Complex.conjCLE.contDiff.comp hg
  have hsconj : HasCompactSupport (fun t ↦ conj (g t)) := hs.comp_left (map_zero _)
  have h := quadratic_phase_compact hΛ T hgconj hsconj
  rw [← quadraticPhasePrefactor_eq hΛ] at h
  simp_rw [iteratedDeriv_conj, Complex.norm_conj] at h
  have hint : (∫ s : ℝ,
      Complex.exp (((Λ / 2 * s ^ 2 : ℝ) : ℂ) * Complex.I) * conj (g s)) =
      conj (∫ s : ℝ, Complex.exp (-((Λ / 2 * s ^ 2 : ℝ) : ℂ) * Complex.I) * g s) := by
    rw [← integral_conj]
    congr 1
    funext s
    simp only [map_mul, ← Complex.exp_conj, map_neg, Complex.conj_ofReal,
      Complex.conj_I, neg_mul_neg]
  have hsum : quadraticPhasePrefactor Λ *
      ∑ j ∈ range T, quadraticTaylorCoefficient Λ j * conj (iteratedDeriv (2 * j) g 0) =
      conj (conj (quadraticPhasePrefactor Λ) *
        ∑ j ∈ range T, conj (quadraticTaylorCoefficient Λ j) * iteratedDeriv (2 * j) g 0) := by
    simp only [map_mul, map_sum, Complex.conj_conj]
  rw [hint, hsum, ← map_sub, Complex.norm_conj] at h
  exact h

end FalconerThetaGauge
