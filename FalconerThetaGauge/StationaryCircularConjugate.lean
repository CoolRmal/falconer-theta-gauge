module

public import FalconerThetaGauge.StationaryCircularRemainderBudget

/-! # The second actual localized circle expansion by complex conjugation -/

@[expose] public section

noncomputable section

open MeasureTheory Finset
open scoped ContDiff ComplexConjugate

namespace FalconerThetaGauge

theorem IsDerivativeRegular.conj {A M : ℝ} {k : ℕ} {G : ℝ → ℂ}
    (hG : IsDerivativeRegular A M k G) :
    IsDerivativeRegular A M k (fun t ↦ conj (G t)) := by
  refine ⟨hG.amplitude_nonneg, hG.one_le_scale, Complex.conjCLE.contDiff.comp hG.smooth, ?_⟩
  intro j hj t
  rw [iteratedDeriv_conj, Complex.norm_conj]
  exact hG.bound j hj t

theorem conj_localizedCircleIntegral (χ : ℝ → ℝ) (G : ℝ → ℂ) (φ Λ : ℝ) :
    conj (localizedCircleIntegral χ (fun t ↦ conj (G t)) φ Λ) =
      localizedCircleIntegral χ G φ (-Λ) := by
  rw [localizedCircleIntegral, localizedCircleIntegral]
  let f : ℝ → ℂ := fun t ↦ Complex.exp (-((Λ * Real.cos t : ℝ) : ℂ) * Complex.I) *
    (χ t : ℂ) * conj (G (φ + t))
  have hi : conj (∫ t in -(Real.pi / 3)..Real.pi / 3, f t) =
      ∫ t in -(Real.pi / 3)..Real.pi / 3, conj (f t) := by
    exact (Complex.conjLIE.toLinearIsometry.intervalIntegral_comp_comm f).symm
  change conj (∫ t in -(Real.pi / 3)..Real.pi / 3, f t) = _
  rw [hi]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp [f]
  simp only [map_mul, ← Complex.exp_conj, map_neg, Complex.conj_ofReal,
    Complex.conj_I, Complex.conj_conj, mul_neg, neg_mul, neg_neg, Complex.ofReal_neg]

theorem conj_stationaryPhaseOperator (j : ℕ) (G : ℝ → ℂ) (φ : ℝ) :
    conj (stationaryPhaseOperator j (fun t ↦ conj (G t)) φ) =
      stationaryPhaseConjugateOperator j G φ := by
  simp only [stationaryPhaseOperator, stationaryPhaseConjugateOperator, map_sum,
    map_mul, iteratedDeriv_conj, Complex.conj_conj, stationaryPhaseConjugateCoefficient]
  rfl

/-- The actual negative-sign localized integral has the exact conjugate operators
and the same explicit numerical remainder as the first stationary point. -/
theorem localizedCircleIntegral_conjugate_operator_expansion_explicit
    {T : ℕ} {G : ℝ → ℂ} {A M φ Λ : ℝ}
    (hG : IsDerivativeRegular A M (2 * T + 2) G) (hGsmooth : ContDiff ℝ ∞ G)
    (hΛ : 0 < Λ) :
    ‖localizedCircleIntegral (circularStationaryCutoff (2 * T + 2)) G φ (-Λ) -
      Complex.exp ((Λ : ℂ) * Complex.I) * conj (quadraticPhasePrefactor Λ) *
        ∑ j ∈ range T, (Λ : ℂ)⁻¹ ^ j * stationaryPhaseConjugateOperator j G φ‖ ≤
      A * Real.sqrt (2 / Λ) *
        (401408 * ((T : ℝ) + 1) ^ 4 * M ^ 2) *
          (6272 * (T : ℝ) ^ 3 * M ^ 2 / Λ) ^ T := by
  have h := localizedCircleIntegral_operator_expansion_explicit hG.conj
    (Complex.conjCLE.contDiff.comp hGsmooth) hΛ (φ := φ)
  rw [← Complex.norm_conj] at h
  simp only [map_sub, map_mul, map_sum, map_pow, map_inv₀, Complex.conj_ofReal,
    ← Complex.exp_conj, map_neg, Complex.conj_I, neg_mul_neg,
    conj_localizedCircleIntegral, conj_stationaryPhaseOperator] at h
  exact h

end FalconerThetaGauge
