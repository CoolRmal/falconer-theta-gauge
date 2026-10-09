module

public import FalconerThetaGauge.StationaryCircularFactorialBudget
public import FalconerThetaGauge.StationaryMorseOperatorExpansion

/-! # A genuine explicit numerical budget for the localized circular remainder -/

@[expose] public section

noncomputable section

open scoped ContDiff

namespace FalconerThetaGauge

/-- The literal source budget from Lemma 3.7. -/
def circularStationaryRemainderBase (T : ℕ) (M : ℝ) : ℝ :=
  100000000 * ((T : ℝ) + 1) ^ 4 * M ^ 2

theorem circularStationaryRemainderBase_nonneg (T : ℕ) (M : ℝ) :
    0 ≤ circularStationaryRemainderBase T M := by
  unfold circularStationaryRemainderBase
  positivity

/-- The two actual Morse derivative norms and their exact factorials give this
intermediate bound, before absorbing constants into the source `10^8` budget. -/
theorem localized_stationary_error_scalar_le {T : ℕ} {A M Λ : ℝ}
    (hA : 0 ≤ A) (hM : 1 ≤ M) (hΛ : 0 < Λ) :
    Real.sqrt (2 / Λ) * (2 * Λ)⁻¹ ^ T / (T.factorial : ℝ) *
        (4 * A * (56 * M) ^ (2 * T) * ((2 * T).factorial : ℝ) ^ 2 +
          4 * A * (56 * M) ^ (2 * T + 2) * ((2 * T + 2).factorial : ℝ) ^ 2) ≤
      A * Real.sqrt (2 / Λ) *
        (401408 * ((T : ℝ) + 1) ^ 4 * M ^ 2) *
          (6272 * (T : ℝ) ^ 3 * M ^ 2 / Λ) ^ T := by
  have h56 : 1 ≤ 56 * M := by linarith
  have hfact : ((2 * T).factorial : ℝ) ≤ ((2 * T + 2).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : 2 * T ≤ 2 * T + 2)
  have hterm : 4 * A * (56 * M) ^ (2 * T) * ((2 * T).factorial : ℝ) ^ 2 ≤
      4 * A * (56 * M) ^ (2 * T + 2) * ((2 * T + 2).factorial : ℝ) ^ 2 := by
    gcongr
    omega
  have hfacpos : 0 < (T.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos T
  have hpow : (56 * M) ^ (2 * T + 2) = ((56 * M) ^ 2) ^ T * (56 * M) ^ 2 := by
    rw [pow_add, pow_mul]
  have hbase : (56 * M) ^ 2 * (4 * (T : ℝ) ^ 3) * (2 * Λ)⁻¹ =
      6272 * (T : ℝ) ^ 3 * M ^ 2 / Λ := by
    field_simp
    ring
  calc
    _ ≤ Real.sqrt (2 / Λ) * (2 * Λ)⁻¹ ^ T / (T.factorial : ℝ) *
        (8 * A * (56 * M) ^ (2 * T + 2) * ((2 * T + 2).factorial : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left (by nlinarith [hterm]) (by positivity)
    _ = Real.sqrt (2 / Λ) * (8 * A * (56 * M) ^ (2 * T + 2)) *
        (((2 * T + 2).factorial : ℝ) ^ 2 / (T.factorial : ℝ)) * (2 * Λ)⁻¹ ^ T := by
      ring
    _ ≤ Real.sqrt (2 / Λ) * (8 * A * (56 * M) ^ (2 * T + 2)) *
        ((2 * (T : ℝ) + 2) ^ 4 * (4 * (T : ℝ) ^ 3) ^ T) * (2 * Λ)⁻¹ ^ T := by
      gcongr
      exact factorial_double_add_two_sq_le T
    _ = Real.sqrt (2 / Λ) * (8 * A * (56 * M) ^ 2 * (2 * (T : ℝ) + 2) ^ 4) *
        ((56 * M) ^ 2 * (4 * (T : ℝ) ^ 3) * (2 * Λ)⁻¹) ^ T := by
      rw [hpow]
      simp only [mul_pow]
      ring
    _ = _ := by
      rw [hbase]
      ring

/-- A kernel-checked bound on the actual localized integral and actual source operators. -/
theorem localizedCircleIntegral_operator_expansion_explicit {T : ℕ} {G : ℝ → ℂ}
    {A M φ Λ : ℝ} (hG : IsDerivativeRegular A M (2 * T + 2) G)
    (hGsmooth : ContDiff ℝ ∞ G) (hΛ : 0 < Λ) :
    ‖localizedCircleIntegral (circularStationaryCutoff (2 * T + 2)) G φ Λ -
      Complex.exp (-(Λ : ℂ) * Complex.I) * quadraticPhasePrefactor Λ *
        ∑ j ∈ Finset.range T, (Λ : ℂ)⁻¹ ^ j * stationaryPhaseOperator j G φ‖ ≤
      A * Real.sqrt (2 / Λ) *
        (401408 * ((T : ℝ) + 1) ^ 4 * M ^ 2) *
          (6272 * (T : ℝ) ^ 3 * M ^ 2 / Λ) ^ T :=
  (localizedCircleIntegral_operator_expansion hG hGsmooth hΛ).trans
    (localized_stationary_error_scalar_le hG.amplitude_nonneg hG.one_le_scale hΛ)

end FalconerThetaGauge
