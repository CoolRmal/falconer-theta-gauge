module

public import FalconerThetaGauge.OrthogonalityRadialDerivatives
public import FalconerThetaGauge.ScheduledSymbolRegularity
public import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow

/-! # Genuine integer radial powers in the opposite-sign terms of Estimate 7.8 -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter
open scoped ContDiff Topology

namespace FalconerThetaGauge

theorem contDiffAt_real_zpow (m : ℤ) {r : ℝ} (hr : r ≠ 0) :
    ContDiffAt ℝ ∞ (fun x : ℝ ↦ x ^ m) r := by
  cases m with
  | ofNat m =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact contDiffAt_id.pow m
  | negSucc m =>
    simp only [zpow_negSucc]
    exact (contDiffAt_id.pow (m + 1)).inv (pow_ne_zero _ hr)

theorem iteratedDeriv_real_zpow (m : ℤ) (j : ℕ) (r : ℝ) :
    iteratedDeriv j (fun x : ℝ ↦ x ^ m) r =
      (∏ k ∈ Finset.range j, ((m : ℝ) - k)) * r ^ (m - j) := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_zpow m j isOpen_univ (mem_univ r)

theorem iteratedDeriv_ofReal_zpow (m : ℤ) (j : ℕ) {r : ℝ} (hr : r ≠ 0) :
    iteratedDeriv j (fun x : ℝ ↦ (x ^ m : ℝ) : ℝ → ℂ) r =
      (((∏ k ∈ Finset.range j, ((m : ℝ) - k)) * r ^ (m - j) : ℝ) : ℂ) := by
  rw [iteratedDeriv_ofReal_eq ((contDiffAt_real_zpow m hr).of_le (by simp)),
    iteratedDeriv_real_zpow]

/-- The source integer radial amplitude, with the actual cutoff and `2⁻ᵛ` normalization. -/
def spaceSplittingRadialAmplitude (K v : ℕ) (m : ℤ) (r : ℝ) : ℂ :=
  (((2 : ℝ) ^ v)⁻¹ : ℂ) * (maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) : ℂ) *
    ((r ^ m : ℝ) : ℂ)

theorem spaceSplittingRadialAmplitude_eq_zero (K v : ℕ) (m : ℤ) {r : ℝ}
    (hr : r ∉ Icc ((2 : ℝ) ^ v / 4) (4 * (2 : ℝ) ^ v)) :
    spaceSplittingRadialAmplitude K v m r = 0 := by
  have hs : (0 : ℝ) < 2 ^ v := by positivity
  have hnot : r / (2 : ℝ) ^ v ∉ Icc (1 / 4) 4 := by
    intro hm
    apply hr
    constructor
    · have h := (le_div_iff₀ hs).mp hm.1
      linarith
    · exact (div_le_iff₀ hs).mp hm.2
  simp only [spaceSplittingRadialAmplitude, maskedFrequencyCutoff_eq_zero K hnot,
    Complex.ofReal_zero, mul_zero, zero_mul]

theorem tsupport_spaceSplittingRadialAmplitude_subset (K v : ℕ) (m : ℤ) :
    tsupport (spaceSplittingRadialAmplitude K v m) ⊆
      Icc ((2 : ℝ) ^ v / 4) (4 * (2 : ℝ) ^ v) := by
  apply isClosed_Icc.closure_subset_iff.mpr
  intro r hr
  by_contra hnot
  exact hr (spaceSplittingRadialAmplitude_eq_zero K v m hnot)

theorem hasCompactSupport_spaceSplittingRadialAmplitude (K v : ℕ) (m : ℤ) :
    HasCompactSupport (spaceSplittingRadialAmplitude K v m) :=
  HasCompactSupport.intro isCompact_Icc fun _ hr ↦
    spaceSplittingRadialAmplitude_eq_zero K v m hr

theorem contDiff_spaceSplittingRadialAmplitude (K v : ℕ) (m : ℤ) :
    ContDiff ℝ ∞ (spaceSplittingRadialAmplitude K v m) := by
  apply contDiff_iff_contDiffAt.mpr
  intro r
  by_cases hr : r = 0
  · subst r
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    have hs : (0 : ℝ) < 2 ^ v := by positivity
    have hn : Iio ((2 : ℝ) ^ v / 4) ∈ 𝓝 (0 : ℝ) :=
      Iio_mem_nhds (by positivity)
    filter_upwards [hn] with x hx
    exact spaceSplittingRadialAmplitude_eq_zero K v m (fun h ↦ not_le_of_gt hx h.1)
  · unfold spaceSplittingRadialAmplitude
    apply (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp r
      (((contDiff_maskedFrequencyCutoff K).contDiffAt).comp r
        (contDiffAt_id.div_const _)))).mul
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp r (contDiffAt_real_zpow m hr)

/-- Actual radial integer powers have the source first two derivative bounds. -/
theorem norm_iteratedDeriv_ofReal_zpow_le_two (m : ℤ) {j : ℕ} (hj : j ≤ 2)
    {r : ℝ} (hr : 0 < r) :
    ‖iteratedDeriv j (fun x : ℝ ↦ ((x ^ m : ℝ) : ℂ)) r‖ ≤
      r ^ m * ((|(m : ℝ)| + 1) / r) ^ j := by
  rw [iteratedDeriv_ofReal_zpow m j hr.ne', Complex.norm_real, Real.norm_eq_abs,
    abs_mul, zpow_sub₀ hr.ne', abs_div, abs_of_pos (zpow_pos hr _),
    abs_of_pos (zpow_pos hr _), zpow_natCast]
  have hcoeff : |∏ k ∈ Finset.range j, ((m : ℝ) - k)| ≤ (|(m : ℝ)| + 1) ^ j := by
    interval_cases j
    · simp
    · simp
    · simp only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero,
        Nat.cast_one, sub_zero, abs_mul, one_mul]
      have hbound : |(m : ℝ) - 1| ≤ |(m : ℝ)| + 1 := by
        simpa only [sub_zero, zero_sub, abs_neg, abs_one] using abs_sub_le (m : ℝ) 0 1
      nlinarith [mul_le_mul_of_nonneg_left hbound (abs_nonneg (m : ℝ)), abs_nonneg (m : ℝ)]
  calc
    _ ≤ (|(m : ℝ)| + 1) ^ j * (r ^ m / r ^ j) :=
      mul_le_mul_of_nonneg_right hcoeff
        (div_nonneg (zpow_nonneg hr.le m) (pow_nonneg hr.le j))
    _ = _ := by rw [div_pow]; ring

/-- On the actual dyadic window, every integer radial power has its literal amplitude bound. -/
theorem real_zpow_le_dyadic_window {s r : ℝ} (hs : 0 < s)
    (hr : r ∈ Icc (s / 4) (4 * s)) (m : ℤ) :
    r ^ m ≤ (4 : ℝ) ^ m.natAbs * s ^ m := by
  have hrpos : 0 < r := (by positivity : (0 : ℝ) < s / 4).trans_le hr.1
  cases m with
  | ofNat m =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast, Int.natAbs_natCast]
    simpa only [mul_pow] using pow_le_pow_left₀ hrpos.le hr.2 m
  | negSucc m =>
    simp only [zpow_negSucc, Int.natAbs_negSucc]
    have hrlow : (s / 4) ^ (m + 1) ≤ r ^ (m + 1) :=
      pow_le_pow_left₀ (by positivity) hr.1 _
    have hi := one_div_le_one_div_of_le
      (by positivity : (0 : ℝ) < (s / 4) ^ (m + 1)) hrlow
    simp only [one_div] at hi
    convert hi using 1
    rw [div_pow]
    field_simp

end FalconerThetaGauge
