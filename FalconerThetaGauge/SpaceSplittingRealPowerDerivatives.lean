module

public import FalconerThetaGauge.SpaceSplittingRealPowerBounds
public import FalconerThetaGauge.SpaceSplittingRadialRegularity

/-! # All actual real-power radial derivatives needed in the separated-scale case -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped ContDiff

namespace FalconerThetaGauge

theorem norm_iteratedDeriv_spaceSplittingRealPowerAmplitude_le {T K v k : ℕ}
    (hT : 1 ≤ T) (hK : 6 * T ≤ K) (hk : k ≤ 6 * T) {α : ℝ}
    (hα : |α| ≤ 2 * T) {r : ℝ}
    (hr : r ∈ tsupport (spaceSplittingRealPowerAmplitude K v α)) :
    ‖iteratedDeriv k (spaceSplittingRealPowerAmplitude K v α) r‖ ≤
      ((4 : ℝ) ^ |α| * ((2 : ℝ) ^ v) ^ α / (2 : ℝ) ^ v) *
        (600 * (T : ℝ) ^ 2 / (2 : ℝ) ^ v) ^ k := by
  let s : ℝ := (2 : ℝ) ^ v
  have hs : 0 < s := by dsimp [s]; positivity
  have hr' : r ∈ Set.Icc (s / 4) (4 * s) :=
    tsupport_spaceSplittingRealPowerAmplitude_subset K v α hr
  have hrpos : 0 < r := (by positivity : 0 < s / 4).trans_le hr'.1
  let f : ℝ → ℂ := fun x ↦ (maskedFrequencyCutoff K (x / s) : ℂ)
  let g : ℝ → ℂ := fun x ↦ ((x ^ α : ℝ) : ℂ)
  have hf : ContDiffAt ℝ ∞ f r := (Complex.ofRealCLM.contDiff.comp
    ((contDiff_maskedFrequencyCutoff K).comp (contDiff_id.div_const s))).contDiffAt
  have hg : ContDiffAt ℝ ∞ g r := Complex.ofRealCLM.contDiff.contDiffAt.comp r
    (Real.contDiffAt_rpow_const_of_ne hrpos.ne')
  have hprod := norm_iteratedDeriv_mul_le_contDiffAt (A := 1)
    (B := (4 : ℝ) ^ |α| * s ^ α) hf hg (by norm_num)
    (by positivity : 0 ≤ 504 * (T : ℝ) ^ 2 / s) k
    (fun l hl ↦ by simpa only [one_mul] using
      norm_iteratedDeriv_scaled_frequencyCutoff_le hK (hl.trans hk) hs r)
    (fun l hl ↦ norm_iteratedDeriv_ofReal_rpow_le_scale (hl.trans hk) hα hs hr')
  have heq : spaceSplittingRealPowerAmplitude K v α =
      fun x ↦ ((s⁻¹ : ℝ) : ℂ) * (f * g) x := by
    funext x
    dsimp only [spaceSplittingRealPowerAmplitude, s, f, g, Pi.mul_apply]
    ring
  rw [heq, iteratedDeriv_const_mul_field, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)]
  calc
    _ ≤ s⁻¹ * ((1 * ((4 : ℝ) ^ |α| * s ^ α)) *
        (504 * (T : ℝ) ^ 2 / s + 32 * T / s) ^ k) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ ≤ s⁻¹ * (((4 : ℝ) ^ |α| * s ^ α) * (600 * (T : ℝ) ^ 2 / s) ^ k) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simp only [one_mul]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ hs.le
      have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
      nlinarith
    _ = _ := by change _ = ((4 : ℝ) ^ |α| * s ^ α / s) * _; ring

/-- The actual radial amplitude in one Case A stationary term. -/
def spaceSplittingCaseAAmplitude (K v j : ℕ) : ℝ → ℂ :=
  spaceSplittingRealPowerAmplitude K v ((3 / 2 : ℝ) - j)

/-- The literal source amplitude envelope before rewriting powers of two. -/
def spaceSplittingCaseABound (v j : ℕ) : ℝ :=
  8 * (4 : ℝ) ^ j * ((2 : ℝ) ^ v) ^ ((3 / 2 : ℝ) - j) / (2 : ℝ) ^ v

theorem caseA_radialWindowCoefficient_le (j : ℕ) :
    (4 : ℝ) ^ |(3 / 2 : ℝ) - j| ≤ 8 * (4 : ℝ) ^ j := by
  have hα : |(3 / 2 : ℝ) - j| ≤ (3 / 2 : ℝ) + j := by
    have hh := abs_sub_le (3 / 2 : ℝ) 0 (j : ℝ)
    simpa only [sub_zero, zero_sub, abs_neg, Nat.abs_cast, abs_of_nonneg
      (by norm_num : (0 : ℝ) ≤ 3 / 2)] using hh
  calc
    _ ≤ (4 : ℝ) ^ ((3 / 2 : ℝ) + j) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hα
    _ = _ := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 4), Real.rpow_natCast]
      congr 1
      norm_num

theorem norm_iteratedDeriv_spaceSplittingCaseAAmplitude_le {T K v j k : ℕ}
    (hT : 1 ≤ T) (hK : 6 * T ≤ K) (hj : j < T) (hk : k ≤ 6 * T) {r : ℝ}
    (hr : r ∈ tsupport (spaceSplittingCaseAAmplitude K v j)) :
    ‖iteratedDeriv k (spaceSplittingCaseAAmplitude K v j) r‖ ≤
      spaceSplittingCaseABound v j * (600 * (T : ℝ) ^ 2 / (2 : ℝ) ^ v) ^ k := by
  have h := norm_iteratedDeriv_spaceSplittingRealPowerAmplitude_le hT hK hk
    (caseA_radial_exponent_abs_le hT hj) hr
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (caseA_radialWindowCoefficient_le j) (by positivity))
    (by positivity)

end FalconerThetaGauge
