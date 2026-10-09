module

public import FalconerThetaGauge.StationaryCircularExpansion

/-! # The literal numerical remainder budget in source Lemma 3.7 -/

@[expose] public section

noncomputable section

open MeasureTheory Finset Function
open scoped ContDiff ComplexConjugate

namespace FalconerThetaGauge

theorem truncation_cube_le_fourth (T : ℕ) : (T : ℝ) ^ 3 ≤ ((T : ℝ) + 1) ^ 4 := by
  have hfirst : (T : ℝ) ^ 3 ≤ ((T : ℝ) + 1) ^ 3 :=
    pow_le_pow_left₀ (Nat.cast_nonneg T) (by linarith) 3
  have hlast : ((T : ℝ) + 1) ^ 3 ≤ ((T : ℝ) + 1) ^ 4 :=
    pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) T]) (by norm_num)
  exact hfirst.trans hlast

theorem localized_stationary_source_budget {T : ℕ} {A M Λ : ℝ}
    (hA : 0 ≤ A) (hM : 1 ≤ M) (hΛ : 0 < Λ) :
    A * Real.sqrt (2 / Λ) *
        (401408 * ((T : ℝ) + 1) ^ 4 * M ^ 2) *
          (6272 * (T : ℝ) ^ 3 * M ^ 2 / Λ) ^ T ≤
      A * Real.sqrt (2 * Real.pi / Λ) * (circularStationaryRemainderBase T M / 4) *
        (circularStationaryRemainderBase T M / Λ) ^ T := by
  have hroot : Real.sqrt (2 / Λ) ≤ Real.sqrt (2 * Real.pi / Λ) := by
    apply Real.sqrt_le_sqrt
    gcongr
    linarith [Real.pi_gt_three]
  have hfront : 401408 * ((T : ℝ) + 1) ^ 4 * M ^ 2 ≤
      circularStationaryRemainderBase T M / 4 := by
    dsimp [circularStationaryRemainderBase]
    nlinarith [mul_nonneg (pow_nonneg (show 0 ≤ (T : ℝ) + 1 by positivity) 4)
      (sq_nonneg M)]
  have hbase : 6272 * (T : ℝ) ^ 3 * M ^ 2 ≤ circularStationaryRemainderBase T M := by
    calc
      _ ≤ 6272 * ((T : ℝ) + 1) ^ 4 * M ^ 2 := by
        gcongr
        exact truncation_cube_le_fourth T
      _ ≤ _ := by
        dsimp [circularStationaryRemainderBase]
        nlinarith [mul_nonneg (pow_nonneg (show 0 ≤ (T : ℝ) + 1 by positivity) 4)
          (sq_nonneg M)]
  have hB := circularStationaryRemainderBase_nonneg T M
  gcongr

theorem circularStationary_away_base_le {T : ℕ} {M : ℝ} (hM : 1 ≤ M) :
    6 * ((T : ℝ) + 2) ^ 2 *
        max (circularStationaryAwayDerivativeScale (2 * T + 2) + M) 3 ≤
      1584 * ((T : ℝ) + 1) ^ 4 * M ^ 2 := by
  let R : ℝ := (T : ℝ) + 1
  have hR : 1 ≤ R := by dsimp [R]; linarith [Nat.cast_nonneg (α := ℝ) T]
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  have hM2 : 1 ≤ M ^ 2 := one_le_pow₀ hM
  have hRM : 1 ≤ R ^ 2 * M ^ 2 := by
    simpa only [mul_one] using
      mul_le_mul hR2 hM2 (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg R)
  have hMM : M ≤ M ^ 2 := by nlinarith
  have hRMM : M ≤ R ^ 2 * M ^ 2 :=
    hMM.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hR2) (sq_nonneg M)])
  have hpi : 16 * Real.pi * R ^ 2 ≤ 64 * (R ^ 2 * M ^ 2) := by
    have h' := mul_le_mul_of_nonneg_right
      (show 16 * Real.pi ≤ (64 : ℝ) by linarith [Real.pi_lt_four]) (sq_nonneg R)
    have h'' := mul_le_mul_of_nonneg_left hM2 (by positivity : 0 ≤ 64 * R ^ 2)
    nlinarith
  have hscale : circularStationaryAwayDerivativeScale (2 * T + 2) + M ≤
      66 * R ^ 2 * M ^ 2 := by
    have heq : circularStationaryAwayDerivativeScale (2 * T + 2) = 1 + 16 * Real.pi * R ^ 2 := by
      simp only [circularStationaryAwayDerivativeScale, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat, R]
      ring
    rw [heq]
    nlinarith
  have hmax : max (circularStationaryAwayDerivativeScale (2 * T + 2) + M) 3 ≤
      66 * R ^ 2 * M ^ 2 := max_le hscale (by nlinarith)
  have horder : ((T : ℝ) + 2) ^ 2 ≤ 4 * R ^ 2 := by
    have ht : 0 ≤ (T : ℝ) := Nat.cast_nonneg T
    dsimp [R]
    nlinarith
  calc
    _ ≤ 6 * (4 * R ^ 2) * (66 * R ^ 2 * M ^ 2) := by gcongr
    _ = _ := by dsimp [R]; ring

theorem inv_le_stationary_square_root {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    Λ⁻¹ ≤ Real.sqrt (2 * Real.pi / Λ) := by
  have hpos : 0 < Λ := by linarith
  have hi : Λ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hΛ
  have hipi : Λ⁻¹ ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  calc
    Λ⁻¹ = Real.sqrt ((Λ⁻¹) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ _ := by
      apply Real.sqrt_le_sqrt
      rw [pow_two, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hipi (by positivity)

/-- Use one extra available integration by parts to retain the actual Gaussian
square-root normalization in the final source error. -/
theorem away_stationary_source_budget {T : ℕ} {A M Λ : ℝ}
    (hA : 0 ≤ A) (hM : 1 ≤ M) (hΛ : 1 ≤ Λ) :
    2 * Real.pi * A *
        (6 * ((T : ℝ) + 2) ^ 2 *
          max (circularStationaryAwayDerivativeScale (2 * T + 2) + M) 3 / Λ) ^ (T + 1) ≤
      A * Real.sqrt (2 * Real.pi / Λ) * (circularStationaryRemainderBase T M / 4) *
        (circularStationaryRemainderBase T M / Λ) ^ T := by
  let c := 6 * ((T : ℝ) + 2) ^ 2 *
    max (circularStationaryAwayDerivativeScale (2 * T + 2) + M) 3
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hc_bound : c ≤ 1584 * ((T : ℝ) + 1) ^ 4 * M ^ 2 :=
    circularStationary_away_base_le hM
  have hc_base : c ≤ circularStationaryRemainderBase T M := by
    apply hc_bound.trans
    dsimp [circularStationaryRemainderBase]
    nlinarith [mul_nonneg (pow_nonneg (show 0 ≤ (T : ℝ) + 1 by positivity) 4)
      (sq_nonneg M)]
  have hc_front : 2 * Real.pi * c ≤ circularStationaryRemainderBase T M / 4 := by
    calc
      _ ≤ 8 * (1584 * ((T : ℝ) + 1) ^ 4 * M ^ 2) := by
        apply mul_le_mul (by linarith [Real.pi_lt_four]) hc_bound hc (by norm_num)
      _ ≤ _ := by
        dsimp [circularStationaryRemainderBase]
        nlinarith [mul_nonneg (pow_nonneg (show 0 ≤ (T : ℝ) + 1 by positivity) 4)
          (sq_nonneg M)]
  have hpos : 0 < Λ := by linarith
  have hB := circularStationaryRemainderBase_nonneg T M
  have hsqrt := inv_le_stationary_square_root hΛ
  change 2 * Real.pi * A * (c / Λ) ^ (T + 1) ≤ _
  calc
    _ = A * Λ⁻¹ * (2 * Real.pi * c) * (c / Λ) ^ T := by
      rw [pow_succ]
      ring
    _ ≤ _ := by
      gcongr

/-- The full literal two-stationary-point expansion obeys the source `10^8` budget,
including the actual remaining full-circle integral and Gaussian normalization. -/
theorem circularIntegral_operator_expansion_source_budget {T : ℕ} {G : ℝ → ℂ}
    {A M φ Λ : ℝ} (hG : IsDerivativeRegular A M (2 * T + 2) G)
    (hGsmooth : ContDiff ℝ ∞ G) (hGP : Periodic G (2 * Real.pi))
    (hΛ : 1 ≤ Λ) (u : ℝ) :
    ‖(∫ t in u..u + 2 * Real.pi,
      Complex.exp ((circularOscillatoryPhase Λ φ t : ℝ) * Complex.I) * G t) -
      (Complex.exp (-(Λ : ℂ) * Complex.I) * quadraticPhasePrefactor Λ *
        ∑ j ∈ range T, (Λ : ℂ)⁻¹ ^ j * stationaryPhaseOperator j G φ +
      Complex.exp ((Λ : ℂ) * Complex.I) * conj (quadraticPhasePrefactor Λ) *
        ∑ j ∈ range T, (Λ : ℂ)⁻¹ ^ j *
          stationaryPhaseConjugateOperator j G (φ + Real.pi))‖ ≤
      A * Real.sqrt (2 * Real.pi / Λ) * circularStationaryRemainderBase T M *
        (circularStationaryRemainderBase T M / Λ) ^ T := by
  have hpos : 0 < Λ := by linarith
  apply (circularIntegral_operator_expansion_intermediate hG hGsmooth hGP hpos u).trans
  have hlocal := localized_stationary_source_budget (T := T)
    hG.amplitude_nonneg hG.one_le_scale hpos
  have haway := away_stationary_source_budget (T := T)
    hG.amplitude_nonneg hG.one_le_scale hΛ
  have hnonneg : 0 ≤ A * Real.sqrt (2 * Real.pi / Λ) *
      circularStationaryRemainderBase T M * (circularStationaryRemainderBase T M / Λ) ^ T := by
    have := hG.amplitude_nonneg
    have := circularStationaryRemainderBase_nonneg T M
    positivity
  nlinarith [hlocal, haway]

end FalconerThetaGauge
