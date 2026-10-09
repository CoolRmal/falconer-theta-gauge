module

public import FalconerThetaGauge.StationaryCircularConjugate
public import FalconerThetaGauge.CircularStationaryPartitionIntegrals

/-! # The genuine full-circle expansion with both stationary points and the away error -/

@[expose] public section

noncomputable section

open MeasureTheory Finset Function
open scoped ContDiff ComplexConjugate

namespace FalconerThetaGauge

/-- The true full-circle integral has the manuscript's two actual universal operators,
with an explicit intermediate error paid by the proved Morse and away estimates. -/
theorem circularIntegral_operator_expansion_intermediate {T : ℕ} {G : ℝ → ℂ}
    {A M φ Λ : ℝ} (hG : IsDerivativeRegular A M (2 * T + 2) G)
    (hGsmooth : ContDiff ℝ ∞ G) (hGP : Periodic G (2 * Real.pi))
    (hΛ : 0 < Λ) (u : ℝ) :
    ‖(∫ t in u..u + 2 * Real.pi,
      Complex.exp ((circularOscillatoryPhase Λ φ t : ℝ) * Complex.I) * G t) -
      (Complex.exp (-(Λ : ℂ) * Complex.I) * quadraticPhasePrefactor Λ *
        ∑ j ∈ range T, (Λ : ℂ)⁻¹ ^ j * stationaryPhaseOperator j G φ +
      Complex.exp ((Λ : ℂ) * Complex.I) * conj (quadraticPhasePrefactor Λ) *
        ∑ j ∈ range T, (Λ : ℂ)⁻¹ ^ j *
          stationaryPhaseConjugateOperator j G (φ + Real.pi))‖ ≤
      2 * (A * Real.sqrt (2 / Λ) *
        (401408 * ((T : ℝ) + 1) ^ 4 * M ^ 2) *
          (6272 * (T : ℝ) ^ 3 * M ^ 2 / Λ) ^ T) +
        2 * Real.pi * A *
          (6 * ((T : ℝ) + 2) ^ 2 *
            max (circularStationaryAwayDerivativeScale (2 * T + 2) + M) 3 / Λ) ^ (T + 1) := by
  have hpart := circularStationary_integral_eq_localized_add_away (2 * T + 2)
    hGsmooth.continuous hGP φ Λ u
  have hpos := localizedCircleIntegral_operator_expansion_explicit hG hGsmooth hΛ (φ := φ)
  have hneg := localizedCircleIntegral_conjugate_operator_expansion_explicit
    hG hGsmooth hΛ (φ := φ + Real.pi)
  have haway := norm_circularStationaryAway_integral_le hΛ hGsmooth hGP hG
    (by omega : T + 1 ≤ 2 * T + 2) φ u
  simp only [Nat.cast_add, Nat.cast_one] at haway
  have hindex : (T : ℝ) + 1 + 1 = (T : ℝ) + 2 := by ring
  rw [hindex] at haway
  rw [hpart]
  have heq (a b c p q : ℂ) : a + b + c - (p + q) = (a - p) + (b - q) + c := by ring
  rw [heq]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  nlinarith [hpos, hneg, haway]

end FalconerThetaGauge
