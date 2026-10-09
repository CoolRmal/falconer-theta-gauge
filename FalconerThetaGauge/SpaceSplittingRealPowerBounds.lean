module

public import FalconerThetaGauge.SpaceSplittingRealPower

/-! # Genuine real radial powers on the actual dyadic cutoff window -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset

namespace FalconerThetaGauge

theorem real_rpow_le_dyadic_window {s r : ℝ} (hs : 0 < s)
    (hr : r ∈ Set.Icc (s / 4) (4 * s)) (α : ℝ) :
    r ^ α ≤ (4 : ℝ) ^ |α| * s ^ α := by
  have hrpos : 0 < r := (by positivity : 0 < s / 4).trans_le hr.1
  by_cases hα : 0 ≤ α
  · calc
      _ ≤ (4 * s) ^ α := Real.rpow_le_rpow hrpos.le hr.2 hα
      _ = _ := by rw [Real.mul_rpow (by norm_num) hs.le, abs_of_nonneg hα]
  · have hα' : α ≤ 0 := le_of_not_ge hα
    calc
      _ ≤ (s / 4) ^ α := Real.rpow_le_rpow_of_nonpos (by positivity) hr.1 hα'
      _ = _ := by
        rw [Real.div_rpow hs.le (by norm_num), abs_of_nonpos hα',
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
        ring

theorem norm_iteratedDeriv_ofReal_rpow_le_scale {T k : ℕ} (hk : k ≤ 6 * T)
    {α : ℝ} (hα : |α| ≤ 2 * T) {s r : ℝ} (hs : 0 < s)
    (hr : r ∈ Set.Icc (s / 4) (4 * s)) :
    ‖iteratedDeriv k (fun x : ℝ ↦ ((x ^ α : ℝ) : ℂ)) r‖ ≤
      ((4 : ℝ) ^ |α| * s ^ α) * (32 * T / s) ^ k := by
  have hrpos : 0 < r := (by positivity : 0 < s / 4).trans_le hr.1
  have hcoeff : |∏ l ∈ range k, (α - l)| ≤ (8 * T) ^ k := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _l ∈ range k, (8 * (T : ℝ)) := by
        apply Finset.prod_le_prod₀ (fun _ _ ↦ abs_nonneg _)
        intro l hl
        have hl' : (l : ℝ) ≤ 6 * T := by
          exact_mod_cast (le_trans (mem_range.1 hl).le hk)
        have hh : |α - l| ≤ |α| + l := by
          simpa only [sub_zero, zero_sub, abs_neg, Nat.abs_cast] using abs_sub_le α 0 l
        linarith
      _ = _ := by simp
  rw [iteratedDeriv_ofReal_rpow α k hrpos.ne', Complex.norm_real, Real.norm_eq_abs,
    abs_mul, Real.rpow_sub hrpos, Real.rpow_natCast, abs_div,
    abs_of_pos (Real.rpow_pos_of_pos hrpos α), abs_of_pos (pow_pos hrpos k)]
  calc
    _ ≤ (8 * T) ^ k * (r ^ α / r ^ k) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = r ^ α * (8 * T / r) ^ k := by rw [div_pow]; ring
    _ ≤ ((4 : ℝ) ^ |α| * s ^ α) * (32 * T / s) ^ k := by
      apply mul_le_mul (real_rpow_le_dyadic_window hs hr α) _ (by positivity) (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      apply (div_le_iff₀ hrpos).2
      have heq : (32 * (T : ℝ) / s) * (s / 4) = 8 * T := by field_simp; ring
      rw [← heq]
      exact mul_le_mul_of_nonneg_left hr.1 (by positivity)

theorem caseA_radial_exponent_abs_le {T j : ℕ} (hT : 1 ≤ T) (hj : j < T) :
    |(3 / 2 : ℝ) - j| ≤ 2 * T := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hj' : (j : ℝ) < T := by exact_mod_cast hj
  apply abs_le.mpr
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) j]

theorem caseA_radial_power_window_le {s r : ℝ} (hs : 0 < s)
    (hr : r ∈ Set.Icc (s / 4) (4 * s)) (j : ℕ) :
    r ^ ((3 / 2 : ℝ) - j) ≤ 8 * (4 : ℝ) ^ j * s ^ ((3 / 2 : ℝ) - j) := by
  have hα : |(3 / 2 : ℝ) - j| ≤ (3 / 2 : ℝ) + j := by
    have hh := abs_sub_le (3 / 2 : ℝ) 0 (j : ℝ)
    simpa only [sub_zero, zero_sub, abs_neg, Nat.abs_cast, abs_of_nonneg
      (by norm_num : (0 : ℝ) ≤ 3 / 2)] using hh
  have hp : (4 : ℝ) ^ |(3 / 2 : ℝ) - j| ≤ 8 * (4 : ℝ) ^ j := by
    calc
      _ ≤ (4 : ℝ) ^ ((3 / 2 : ℝ) + j) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hα
      _ = _ := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 4), Real.rpow_natCast]
        congr 1
        norm_num
  exact (real_rpow_le_dyadic_window hs hr _).trans
    (mul_le_mul_of_nonneg_right hp (by positivity))

end FalconerThetaGauge
