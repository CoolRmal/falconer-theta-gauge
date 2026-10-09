/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierSeparationFullSeriesBudget

/-! # The literal inverse Fourier coefficient decay and total 1.1 budget -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric Polynomial Finset
open scoped Classical ContDiff

namespace FalconerThetaGauge

def scheduledPairCommonScale (T : ℕ) (E : ℝ) (I₁ I₂ : Finset ProfileScheduleTest)
    (L₁ L₂ : ℕ) : ℝ :=
  max (max 1 (scheduledSymbolScale T E I₁ L₁)) (max 1 (scheduledSymbolScale T E I₂ L₂))

theorem one_le_scheduledPairCommonScale (T : ℕ) (E : ℝ)
    (I₁ I₂ : Finset ProfileScheduleTest) (L₁ L₂ : ℕ) :
    1 ≤ scheduledPairCommonScale T E I₁ I₂ L₁ L₂ :=
  (le_max_left _ _).trans (le_max_left _ _)

theorem scheduledSymbolScale_left_le_common (T : ℕ) (E : ℝ)
    (I₁ I₂ : Finset ProfileScheduleTest) (L₁ L₂ : ℕ) :
    scheduledSymbolScale T E I₁ L₁ ≤ scheduledPairCommonScale T E I₁ I₂ L₁ L₂ :=
  (le_max_right _ _).trans (le_max_left _ _)

theorem scheduledSymbolScale_right_le_common (T : ℕ) (E : ℝ)
    (I₁ I₂ : Finset ProfileScheduleTest) (L₁ L₂ : ℕ) :
    scheduledSymbolScale T E I₂ L₂ ≤ scheduledPairCommonScale T E I₁ I₂ L₁ L₂ :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem scheduledPairCommonScale_le_frequency {T : ℕ} (hT : 1 ≤ T) (N : ℕ)
    {E w : ℝ} (hE : 0 ≤ E) (hw : 10 * E ≤ w)
    (I₁ I₂ : Finset ProfileScheduleTest) {L₁ L₂ : ℕ}
    (hc₁ : I₁.card ≤ N ^ 2 + 1) (hc₂ : I₂.card ≤ N ^ 2 + 1)
    (hL₁ : 2 * (L₁ : ℝ) ≤ w + E) (hL₂ : 2 * (L₂ : ℝ) ≤ w + E) :
    scheduledPairCommonScale T E I₁ I₂ L₁ L₂ ≤
      128 * (T : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1) * (2 : ℝ) ^ (w / 2 - E / 2) := by
  have hF : 1 ≤ (2 : ℝ) ^ (w / 2 - E / 2) :=
    Real.one_le_rpow (by norm_num) (by linarith)
  exact max_le
    (scheduledSymbolScale_max_one_le hT N E I₁ L₁ hc₁ hF
      (scheduled_mask_frequency_factor_le hE hw hL₁))
    (scheduledSymbolScale_max_one_le hT N E I₂ L₂ hc₂ hF
      (scheduled_mask_frequency_factor_le hE hw hL₂))

theorem mattila_coefficient_polynomial_le_sourceBudget (T N : ℕ) :
    9600 * (128 : ℝ) ^ 2 * (T : ℝ) ^ 5 * ((N : ℝ) ^ 2 + 1) ^ 2 ≤
      (2 : ℝ) ^ (80 : ℕ) * ((T : ℝ) + 1) ^ (12 : ℕ) *
        ((N : ℝ) + 16) ^ (12 : ℕ) := by
  have hT : (T : ℝ) ^ 5 ≤ ((T : ℝ) + 1) ^ 12 := by
    calc
      _ ≤ ((T : ℝ) + 1) ^ 5 :=
        pow_le_pow_left₀ (Nat.cast_nonneg T) (by linarith) 5
      _ ≤ _ := pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) T; linarith)
        (by norm_num : 5 ≤ 12)
  have hN : ((N : ℝ) ^ 2 + 1) ^ 2 ≤ ((N : ℝ) + 16) ^ 12 := by
    calc
      _ ≤ (((N : ℝ) + 16) ^ 2) ^ 2 := by
        gcongr
        nlinarith [Nat.cast_nonneg (α := ℝ) N]
      _ = ((N : ℝ) + 16) ^ 4 := by ring
      _ ≤ _ := pow_le_pow_right₀
        (by have := Nat.cast_nonneg (α := ℝ) N; linarith) (by norm_num : 4 ≤ 12)
  gcongr
  norm_num

theorem mattila_coefficient_base_le {T N : ℕ} {E w M : ℝ} (hM₀ : 0 ≤ M)
    (hM : M ≤ 128 * (T : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1) *
      (2 : ℝ) ^ (w / 2 - E / 2))
    (hP1 : (2 : ℝ) ^ (80 : ℕ) * ((T : ℝ) + 1) ^ (12 : ℕ) *
      ((N : ℝ) + 16) ^ (12 : ℕ) ≤ (2 : ℝ) ^ (E / 8)) :
    9600 * T * M ^ 2 * (2 : ℝ) ^ (-w) ≤ (2 : ℝ) ^ (-(7 * E / 8)) := by
  have hpower : ((2 : ℝ) ^ (w / 2 - E / 2)) ^ (2 : ℕ) * (2 : ℝ) ^ (-w) =
      (2 : ℝ) ^ (-E) := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_add (by norm_num)]
    congr 1
    norm_num
    ring
  calc
    _ ≤ 9600 * T *
        (128 * (T : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1) *
          (2 : ℝ) ^ (w / 2 - E / 2)) ^ 2 * (2 : ℝ) ^ (-w) := by gcongr
    _ = (9600 * (128 : ℝ) ^ 2 * (T : ℝ) ^ 5 * ((N : ℝ) ^ 2 + 1) ^ 2) *
        (2 : ℝ) ^ (-E) := by
      calc
        _ = (9600 * (128 : ℝ) ^ 2 * (T : ℝ) ^ 5 * ((N : ℝ) ^ 2 + 1) ^ 2) *
            (((2 : ℝ) ^ (w / 2 - E / 2)) ^ (2 : ℕ) * (2 : ℝ) ^ (-w)) := by ring
        _ = _ := by rw [hpower]
    _ ≤ (2 : ℝ) ^ (E / 8) * (2 : ℝ) ^ (-E) :=
      mul_le_mul_of_nonneg_right
        ((mattila_coefficient_polynomial_le_sourceBudget T N).trans hP1) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by norm_num)]; congr 1; ring

theorem finite_geometric_sum_le_one_point_one (T : ℕ) {q : ℝ} (hq₀ : 0 ≤ q)
    (hq : q ≤ 1 / 11) : (∑ j ∈ range T, q ^ j) ≤ 11 / 10 := by
  have hq₁ : q < 1 := by linarith
  calc
    _ ≤ ∑' j : ℕ, q ^ j :=
      (summable_geometric_of_lt_one hq₀ hq₁).sum_le_tsum _ (fun _ _ ↦ pow_nonneg hq₀ _)
    _ = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq₀ hq₁
    _ ≤ _ := by
      rw [← one_div, div_le_iff₀ (by linarith : 0 < 1 - q)]
      nlinarith

theorem source_coefficient_decay_sum_le (T : ℕ) {E : ℝ} (hE : 16 ≤ E) :
    (∑ j ∈ range T, ((2 : ℝ) ^ (-(7 * E / 8))) ^ j) ≤ 11 / 10 := by
  apply finite_geometric_sum_le_one_point_one T (by positivity)
  calc
    _ ≤ (2 : ℝ) ^ (-4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ ≤ _ := by norm_num

end FalconerThetaGauge
