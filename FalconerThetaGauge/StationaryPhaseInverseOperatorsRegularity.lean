/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.PolynomialDifferentialActionFinite
public import FalconerThetaGauge.PolynomialWeightedNorm
public import FalconerThetaGauge.StationaryPhaseInverseOperatorsConjugate

/-! # Actual derivative regularity of the stationary and inverse operators -/

@[expose] public section

noncomputable section

open Finset Polynomial
open scoped ContDiff

namespace FalconerThetaGauge

/-- Applying a polynomial of order `d` consumes exactly `d` input derivatives and
multiplies the amplitude bound by its literal weighted coefficient norm. -/
theorem polynomialDifferentialAction_isDerivativeRegular {G : ℝ → ℂ}
    {A M : ℝ} {K d : ℕ} (hG : IsDerivativeRegular A M (K + d) G)
    (p : Polynomial ℂ) (hp : p.natDegree ≤ d) :
    IsDerivativeRegular (A * polynomialWeightedNorm p M) M K
      (polynomialDifferentialAction p G) := by
  have hM : 0 ≤ M := by linarith [hG.one_le_scale]
  refine ⟨mul_nonneg hG.amplitude_nonneg (polynomialWeightedNorm_nonneg p hM),
    hG.one_le_scale, contDiff_polynomialDifferentialAction_of_natDegree_le hG.smooth p hp, ?_⟩
  intro m hm x
  rw [iteratedDeriv_polynomialDifferentialAction_of_natDegree_le hG.smooth p hp hm]
  calc
    _ ≤ ∑ n ∈ p.support, ‖p.coeff n * iteratedDeriv (m + n) G x‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ p.support, ‖p.coeff n‖ * (A * M ^ (m + n)) := by
      apply sum_le_sum
      intro n hn
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply hG.bound
      have hnd := (le_natDegree_of_mem_supp n hn).trans hp
      omega
    _ = (A * polynomialWeightedNorm p M) * M ^ m := by
      rw [polynomialWeightedNorm, Polynomial.sum_def, mul_sum, sum_mul]
      apply sum_congr rfl
      intro n _
      rw [pow_add]
      ring

theorem polynomialWeightedNorm_map_starRingEnd (p : Polynomial ℂ) (M : ℝ) :
    polynomialWeightedNorm (p.map (starRingEnd ℂ)) M = polynomialWeightedNorm p M := by
  rw [polynomialWeightedNorm_eq_sum_range _ M (Polynomial.natDegree_map_le),
    polynomialWeightedNorm_eq_sum_range p M (le_refl _)]
  simp only [Polynomial.coeff_map, starRingEnd_apply, norm_star]

theorem polynomialWeightedNorm_stationaryPhaseConjugateInversePolynomial (j : ℕ) (M : ℝ) :
    polynomialWeightedNorm (stationaryPhaseConjugateInversePolynomial j) M =
      polynomialWeightedNorm (stationaryPhaseInversePolynomial j) M :=
  polynomialWeightedNorm_map_starRingEnd _ _

theorem stationaryPhaseInverseOperator_isDerivativeRegular {G : ℝ → ℂ}
    {A M : ℝ} {K j : ℕ} (hG : IsDerivativeRegular A M (K + 2 * j) G) :
    IsDerivativeRegular (A * polynomialWeightedNorm (stationaryPhaseInversePolynomial j) M)
      M K (stationaryPhaseInverseOperator j G) :=
  polynomialDifferentialAction_isDerivativeRegular hG _
    (stationaryPhaseInversePolynomial_natDegree_le j)

theorem stationaryPhaseConjugateInverseOperator_isDerivativeRegular {G : ℝ → ℂ}
    {A M : ℝ} {K j : ℕ} (hG : IsDerivativeRegular A M (K + 2 * j) G) :
    IsDerivativeRegular (A * polynomialWeightedNorm (stationaryPhaseInversePolynomial j) M)
      M K (stationaryPhaseConjugateInverseOperator j G) := by
  have h := polynomialDifferentialAction_isDerivativeRegular hG
    (stationaryPhaseConjugateInversePolynomial j)
    (stationaryPhaseConjugateInversePolynomial_natDegree_le j)
  simpa only [polynomialWeightedNorm_stationaryPhaseConjugateInversePolynomial,
    stationaryPhaseConjugateInverseOperator] using h

theorem polynomialWeightedNorm_stationaryPhasePolynomial (j : ℕ) (M : ℝ) :
    polynomialWeightedNorm (stationaryPhasePolynomial j) M = stationaryPhaseWeightedNorm j M := by
  rw [polynomialWeightedNorm_eq_sum_range _ M (stationaryPhasePolynomial_natDegree_le j)]
  simp only [stationaryPhasePolynomial_coeff, stationaryPhaseWeightedNorm]

theorem stationaryPhaseOperator_isDerivativeRegular {G : ℝ → ℂ}
    {A M : ℝ} {K j : ℕ} (hG : IsDerivativeRegular A M (K + 2 * j) G) :
    IsDerivativeRegular (A * stationaryPhaseWeightedNorm j M) M K
      (fun φ ↦ stationaryPhaseOperator j G φ) := by
  have h := polynomialDifferentialAction_isDerivativeRegular hG
    (stationaryPhasePolynomial j) (stationaryPhasePolynomial_natDegree_le j)
  simpa only [polynomialWeightedNorm_stationaryPhasePolynomial,
    stationaryPhasePolynomial_action] using h

theorem stationaryPhaseConjugateOperator_isDerivativeRegular {G : ℝ → ℂ}
    {A M : ℝ} {K j : ℕ} (hG : IsDerivativeRegular A M (K + 2 * j) G) :
    IsDerivativeRegular (A * stationaryPhaseWeightedNorm j M) M K
      (fun φ ↦ stationaryPhaseConjugateOperator j G φ) := by
  have hdegree : (stationaryPhaseConjugatePolynomial j).natDegree ≤ 2 * j :=
    Polynomial.natDegree_map_le.trans (stationaryPhasePolynomial_natDegree_le j)
  have hnorm : polynomialWeightedNorm (stationaryPhaseConjugatePolynomial j) M =
      stationaryPhaseWeightedNorm j M :=
    (polynomialWeightedNorm_map_starRingEnd _ _).trans
      (polynomialWeightedNorm_stationaryPhasePolynomial j M)
  have h := polynomialDifferentialAction_isDerivativeRegular hG
    (stationaryPhaseConjugatePolynomial j) hdegree
  simpa only [hnorm, stationaryPhaseConjugatePolynomial_action] using h

theorem IsDerivativeRegular.mono_amplitude {A B M : ℝ} {K : ℕ} {f : ℝ → ℂ}
    (hf : IsDerivativeRegular A M K f) (hAB : A ≤ B) : IsDerivativeRegular B M K f := by
  refine ⟨hf.amplitude_nonneg.trans hAB, hf.one_le_scale, hf.smooth, ?_⟩
  intro j hj x
  exact (hf.bound j hj x).trans (mul_le_mul_of_nonneg_right hAB
    (pow_nonneg (by linarith [hf.one_le_scale]) j))

/-- The source's numerical `Pⱼ` cost bounds the genuine output derivatives. -/
theorem stationaryPhaseOperator_isDerivativeRegular_budget {G : ℝ → ℂ}
    {A M : ℝ} {K j : ℕ} (hG : IsDerivativeRegular A M (K + 2 * j) G) (hj : 1 ≤ j) :
    IsDerivativeRegular (A * (100 * j * M ^ 2) ^ j) M K
      (fun φ ↦ stationaryPhaseOperator j G φ) :=
  (stationaryPhaseOperator_isDerivativeRegular hG).mono_amplitude
    (mul_le_mul_of_nonneg_left (stationaryPhaseWeightedNorm_le hj hG.one_le_scale)
      hG.amplitude_nonneg)

theorem stationaryPhaseConjugateOperator_isDerivativeRegular_budget {G : ℝ → ℂ}
    {A M : ℝ} {K j : ℕ} (hG : IsDerivativeRegular A M (K + 2 * j) G) (hj : 1 ≤ j) :
    IsDerivativeRegular (A * (100 * j * M ^ 2) ^ j) M K
      (fun φ ↦ stationaryPhaseConjugateOperator j G φ) :=
  (stationaryPhaseConjugateOperator_isDerivativeRegular hG).mono_amplitude
    (mul_le_mul_of_nonneg_left (stationaryPhaseWeightedNorm_le hj hG.one_le_scale)
      hG.amplitude_nonneg)

end FalconerThetaGauge
