module

public import FalconerThetaGauge.MaskedMattilaSymbolRegularity
public import FalconerThetaGauge.StationaryPhaseInverseOperatorsRegularity

/-! # Bounds for the genuine coefficients in the space-splitting expansion -/

@[expose] public section

noncomputable section

open MeasureTheory Finset

namespace FalconerThetaGauge

theorem norm_stationaryPhaseOperator_le_of_regular {G : ℝ → ℂ}
    {A M : ℝ} {K j : ℕ} (hG : IsDerivativeRegular A M K G) (hj : 2 * j ≤ K)
    (φ : ℝ) : ‖stationaryPhaseOperator j G φ‖ ≤ A * (100 * j * M ^ 2) ^ j := by
  by_cases hj₀ : j = 0
  · subst j
    simpa only [stationaryPhaseOperator_zero, Nat.cast_zero, mul_zero, zero_mul,
      pow_zero, mul_one, iteratedDeriv_zero] using hG.bound 0 (by omega) φ
  · have h := stationaryPhaseOperator_isDerivativeRegular_budget
      (K := 0) (hG.of_le (by simpa using hj)) (by omega : 1 ≤ j)
    simpa only [iteratedDeriv_zero, pow_zero, mul_one] using h.bound 0 (by omega) φ

theorem norm_stationaryPhaseConjugateOperator_le_of_regular {G : ℝ → ℂ}
    {A M : ℝ} {K j : ℕ} (hG : IsDerivativeRegular A M K G) (hj : 2 * j ≤ K)
    (φ : ℝ) : ‖stationaryPhaseConjugateOperator j G φ‖ ≤
      A * (100 * j * M ^ 2) ^ j := by
  by_cases hj₀ : j = 0
  · subst j
    simpa only [stationaryPhaseConjugateOperator_zero, Nat.cast_zero, mul_zero, zero_mul,
      pow_zero, mul_one, iteratedDeriv_zero] using hG.bound 0 (by omega) φ
  · have h := stationaryPhaseConjugateOperator_isDerivativeRegular_budget
      (K := 0) (hG.of_le (by simpa using hj)) (by omega : 1 ≤ j)
    simpa only [iteratedDeriv_zero, pow_zero, mul_one] using h.bound 0 (by omega) φ

theorem norm_stationaryPhaseOperator_builtPair_le {ρ : Measure Plane} {T : ℕ}
    {E width : ℝ} {I : Finset ProfileScheduleTest} {L : ℕ}
    (hL : ∀ test ∈ I, test.length ≤ L) {b : Plane → UnitCircle → ℝ}
    (hb : b ∈ scheduledSymbolClass ρ E width (8 * T) I (2 * T))
    {j : ℕ} (hj : j < T) (x x' : Plane) (φ : ℝ) :
    ‖stationaryPhaseOperator j (builtSymbolPairAngularAmplitude b b x x') φ‖ ≤
      (400 * j * (max 1 (scheduledSymbolScale T E I L)) ^ 2) ^ j := by
  have h := norm_stationaryPhaseOperator_le_of_regular
    (builtSymbolPairAngularAmplitude_isDerivativeRegular hL hL hb hb x x')
    (by omega : 2 * j ≤ 6 * T) φ
  convert h using 1
  ring

theorem norm_stationaryPhaseConjugateOperator_builtPair_le {ρ : Measure Plane} {T : ℕ}
    {E width : ℝ} {I : Finset ProfileScheduleTest} {L : ℕ}
    (hL : ∀ test ∈ I, test.length ≤ L) {b : Plane → UnitCircle → ℝ}
    (hb : b ∈ scheduledSymbolClass ρ E width (8 * T) I (2 * T))
    {j : ℕ} (hj : j < T) (x x' : Plane) (φ : ℝ) :
    ‖stationaryPhaseConjugateOperator j (builtSymbolPairAngularAmplitude b b x x') φ‖ ≤
      (400 * j * (max 1 (scheduledSymbolScale T E I L)) ^ 2) ^ j := by
  have h := norm_stationaryPhaseConjugateOperator_le_of_regular
    (builtSymbolPairAngularAmplitude_isDerivativeRegular hL hL hb hb x x')
    (by omega : 2 * j ≤ 6 * T) φ
  convert h using 1
  ring

/-- The radial `4ʲ` loss is summable once the actual coefficient scale is small. -/
theorem stationary_coefficient_scaled_le_geometric {c : ℂ} {M d s : ℝ}
    {j T : ℕ} (hd : 0 < d) (hs : 0 < s) (hj : j ≤ T)
    (hc : ‖c‖ ≤ (400 * j * M ^ 2) ^ j)
    (hscale : 1600 * T * M ^ 2 / (s * d) ≤ 1 / 4) :
    ‖c‖ * (4 / (s * d)) ^ j ≤ (1 / (4 : ℝ)) ^ j := by
  have hsd : 0 < s * d := mul_pos hs hd
  calc
    _ ≤ (400 * j * M ^ 2) ^ j * (4 / (s * d)) ^ j :=
      mul_le_mul_of_nonneg_right hc (pow_nonneg (by positivity) _)
    _ = (1600 * j * M ^ 2 / (s * d)) ^ j := by rw [← mul_pow]; congr 1; ring
    _ ≤ (1 / (4 : ℝ)) ^ j := by
      apply pow_le_pow_left₀ (by positivity)
      exact (div_le_div_of_nonneg_right (by
        have hj' : (j : ℝ) ≤ T := by exact_mod_cast hj
        nlinarith [sq_nonneg M]) hsd.le).trans hscale

end FalconerThetaGauge
