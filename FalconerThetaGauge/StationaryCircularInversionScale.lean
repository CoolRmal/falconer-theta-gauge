module

public import FalconerThetaGauge.StationaryCircularInversionNormalized
public import FalconerThetaGauge.ParameterBudgets

/-! # The literal source §7.5 frequency and stationary remainder scales -/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

theorem scheduled_mask_frequency_factor_le {E w : ℝ} (hE : 0 ≤ E)
    (hw : 10 * E ≤ w) {L : ℕ} (hL : 2 * (L : ℝ) ≤ w + E) :
    max 1 ((2 : ℝ) ^ (L : ℝ) * (2 : ℝ) ^ (-E)) ≤
      (2 : ℝ) ^ (w / 2 - E / 2) := by
  apply max_le
  · exact Real.one_le_rpow (by norm_num) (by linarith)
  · rw [← Real.rpow_add (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

theorem prepared_stationary_scale_le {T : ℕ} (hT : 1 ≤ T) (N : ℕ)
    {E w M : ℝ} (hE : 0 ≤ E) (hw : 10 * E ≤ w)
    (hM : M ≤ 256 * (T : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1) *
      (2 : ℝ) ^ (w / 2 - E / 2)) :
    1200 * (T : ℝ) ^ 2 + M ≤
      2048 * (T : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1) * (2 : ℝ) ^ (w / 2 - E / 2) := by
  have hf : 1 ≤ (2 : ℝ) ^ (w / 2 - E / 2) :=
    Real.one_le_rpow (by norm_num) (by linarith)
  have hprod : 1 ≤ ((N : ℝ) ^ 2 + 1) * (2 : ℝ) ^ (w / 2 - E / 2) := by
    nlinarith [sq_nonneg (N : ℝ)]
  have h := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 1792 * (T : ℝ) ^ 2)
  nlinarith

theorem stationary_remainder_polynomial_le_sourceBudget (T N : ℕ) :
    100000000 * 2048 ^ 2 * 16 * ((T : ℝ) + 1) ^ 4 * (T : ℝ) ^ 4 *
      ((N : ℝ) ^ 2 + 1) ^ 2 ≤
      (2 : ℝ) ^ (80 : ℕ) * ((T : ℝ) + 1) ^ (12 : ℕ) *
        ((N : ℝ) + 16) ^ (12 : ℕ) := by
  have hT : (T : ℝ) ^ 4 ≤ ((T : ℝ) + 1) ^ 4 :=
    pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) T)
      (by linarith : (T : ℝ) ≤ (T : ℝ) + 1) 4
  have hN : (N : ℝ) ^ 2 + 1 ≤ ((N : ℝ) + 16) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hTp : ((T : ℝ) + 1) ^ 8 ≤ ((T : ℝ) + 1) ^ 12 :=
    pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) T; linarith)
      (by norm_num : 8 ≤ 12)
  have hNp : ((N : ℝ) + 16) ^ 4 ≤ ((N : ℝ) + 16) ^ 12 :=
    pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
      (by norm_num : 4 ≤ 12)
  calc
    _ ≤ (2 : ℝ) ^ (80 : ℕ) * ((T : ℝ) + 1) ^ 4 * ((T : ℝ) + 1) ^ 4 *
        (((N : ℝ) + 16) ^ 2) ^ 2 := by gcongr; norm_num
    _ = (2 : ℝ) ^ (80 : ℕ) * ((T : ℝ) + 1) ^ 8 * ((N : ℝ) + 16) ^ 4 := by ring
    _ ≤ _ := by gcongr

theorem stationary_frequency_square_ratio (E w : ℝ) :
    ((2 : ℝ) ^ (w / 2 - E / 2)) ^ (2 : ℕ) / (2 : ℝ) ^ (w - 4) =
      16 * (2 : ℝ) ^ (-E) := by
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  norm_num only [Nat.cast_ofNat]
  rw [show (w / 2 - E / 2) * (2 : ℝ) - (w - 4) = 4 + -E by ring,
    Real.rpow_add (by norm_num)]
  norm_num

/-- The actual stationary remainder ratio has the precise source decay, using P1. -/
theorem prepared_stationary_remainder_ratio_le {T N : ℕ} (hT : 1 ≤ T)
    {E w M Λ : ℝ} (hE : 0 ≤ E) (hw : 10 * E ≤ w) (hM₀ : 0 ≤ M)
    (hM : M ≤ 256 * (T : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1) *
      (2 : ℝ) ^ (w / 2 - E / 2)) (hΛ : (2 : ℝ) ^ (w - 4) ≤ Λ)
    (hP1 : (2 : ℝ) ^ (80 : ℕ) * ((T : ℝ) + 1) ^ (12 : ℕ) *
      ((N : ℝ) + 16) ^ (12 : ℕ) ≤ (2 : ℝ) ^ (E / 8)) :
    circularStationaryRemainderBase T (1200 * (T : ℝ) ^ 2 + M) / Λ ≤
      (2 : ℝ) ^ (-(7 * E / 8)) := by
  have hscale := prepared_stationary_scale_le hT N hE hw hM
  have hΛ₀ : 0 < (2 : ℝ) ^ (w - 4) := by positivity
  have hnum : circularStationaryRemainderBase T (1200 * (T : ℝ) ^ 2 + M) ≤
      100000000 * ((T : ℝ) + 1) ^ 4 *
        (2048 * (T : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1) *
          (2 : ℝ) ^ (w / 2 - E / 2)) ^ 2 := by
    unfold circularStationaryRemainderBase
    gcongr
  calc
    _ ≤ (100000000 * ((T : ℝ) + 1) ^ 4 *
        (2048 * (T : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1) *
          (2 : ℝ) ^ (w / 2 - E / 2)) ^ 2) / (2 : ℝ) ^ (w - 4) :=
      div_le_div₀ (circularStationaryRemainderBase_nonneg _ _) hnum hΛ₀ hΛ
    _ = (100000000 * 2048 ^ 2 * 16 * ((T : ℝ) + 1) ^ 4 * (T : ℝ) ^ 4 *
        ((N : ℝ) ^ 2 + 1) ^ 2) * (2 : ℝ) ^ (-E) := by
      calc
        _ = (100000000 * 2048 ^ 2 * ((T : ℝ) + 1) ^ 4 * (T : ℝ) ^ 4 *
            ((N : ℝ) ^ 2 + 1) ^ 2) *
            (((2 : ℝ) ^ (w / 2 - E / 2)) ^ 2 / (2 : ℝ) ^ (w - 4)) := by ring
        _ = _ := by rw [stationary_frequency_square_ratio]; ring
    _ ≤ (2 : ℝ) ^ (E / 8) * (2 : ℝ) ^ (-E) :=
      mul_le_mul_of_nonneg_right
        ((stationary_remainder_polynomial_le_sourceBudget T N).trans hP1) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by norm_num)]; congr 1; ring

end FalconerThetaGauge
