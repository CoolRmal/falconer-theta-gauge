module

public import FalconerThetaGauge.StationaryCircularSourceBudget

/-! # The literal circular stationary phase formula of source Lemma 3.7 -/

@[expose] public section

noncomputable section

open MeasureTheory Finset Function
open scoped ContDiff ComplexConjugate

namespace FalconerThetaGauge

theorem stationaryPhase_positive_prefactor_eq {Λ : ℝ} (hΛ : 0 < Λ) :
    Complex.exp (-(Λ : ℂ) * Complex.I) * quadraticPhasePrefactor Λ =
      (Real.sqrt (2 * Real.pi / Λ) : ℂ) *
        Complex.exp (-((Λ - Real.pi / 4 : ℝ) : ℂ) * Complex.I) := by
  rw [quadraticPhasePrefactor_eq hΛ]
  calc
    _ = (Real.sqrt (2 * Real.pi / Λ) : ℂ) *
        (Complex.exp (-(Λ : ℂ) * Complex.I) *
          Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)) := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      push_cast
      ring

theorem stationaryPhase_negative_prefactor_eq {Λ : ℝ} (hΛ : 0 < Λ) :
    Complex.exp ((Λ : ℂ) * Complex.I) * conj (quadraticPhasePrefactor Λ) =
      (Real.sqrt (2 * Real.pi / Λ) : ℂ) *
        Complex.exp (((Λ - Real.pi / 4 : ℝ) : ℂ) * Complex.I) := by
  rw [quadraticPhasePrefactor_eq hΛ]
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I, mul_neg]
  calc
    _ = (Real.sqrt (2 * Real.pi / Λ) : ℂ) *
        (Complex.exp ((Λ : ℂ) * Complex.I) *
          Complex.exp (-(((Real.pi / 4 : ℝ) : ℂ) * Complex.I))) := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      push_cast
      ring

/-- Source Lemma 3.7 for the actual periodic function and actual differential operators.
The explicit error includes the prefactor; the normalized bracket error is therefore
bounded by `A * B * (B/Λ)^T`, with `B = 10^8(T+1)^4 M²`. -/
theorem circular_stationary_phase {T : ℕ} {G : ℝ → ℂ} {A M φ Λ : ℝ}
    (hG : IsDerivativeRegular A M (2 * T + 2) G) (hGsmooth : ContDiff ℝ ∞ G)
    (hGP : Periodic G (2 * Real.pi)) (hΛ : 1 ≤ Λ) (u : ℝ) :
    ‖(∫ t in u..u + 2 * Real.pi,
      Complex.exp (-((Λ * Real.cos (t - φ) : ℝ) : ℂ) * Complex.I) * G t) -
      (Real.sqrt (2 * Real.pi / Λ) : ℂ) *
        (Complex.exp (-((Λ - Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
          ∑ j ∈ range T, (Λ : ℂ)⁻¹ ^ j * stationaryPhaseOperator j G φ +
        Complex.exp (((Λ - Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
          ∑ j ∈ range T, (Λ : ℂ)⁻¹ ^ j *
            stationaryPhaseConjugateOperator j G (φ + Real.pi))‖ ≤
      A * Real.sqrt (2 * Real.pi / Λ) * circularStationaryRemainderBase T M *
        (circularStationaryRemainderBase T M / Λ) ^ T := by
  have hpos : 0 < Λ := by linarith
  have h := circularIntegral_operator_expansion_source_budget (φ := φ) hG hGsmooth hGP hΛ u
  rw [stationaryPhase_positive_prefactor_eq hpos,
    stationaryPhase_negative_prefactor_eq hpos] at h
  simp only [mul_assoc] at h
  rw [← mul_add] at h
  simpa only [circularOscillatoryPhase, neg_mul, Complex.ofReal_neg, mul_assoc] using h

end FalconerThetaGauge
