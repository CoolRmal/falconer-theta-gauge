module

public import FalconerThetaGauge.ExplicitBumpCutoff
public import Mathlib.Analysis.Real.Pi.Bounds

/-! # The genuine smooth dyadic-frequency cutoff of the source -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter
open scoped ContDiff Convolution

namespace FalconerThetaGauge

/-- The actual source cutoff `1_[3/8,3] * ω_(1/8)`. -/
def maskedFrequencyCutoff (K : ℕ) : ℝ → ℝ :=
  smoothIndicator K (1 / 8) (Icc (3 / 8) 3)

theorem contDiff_maskedFrequencyCutoff (K : ℕ) :
    ContDiff ℝ ∞ (maskedFrequencyCutoff K) :=
  contDiff_smoothIndicator K (by norm_num) measurableSet_Icc

theorem maskedFrequencyCutoff_mem_Icc (K : ℕ) (x : ℝ) :
    maskedFrequencyCutoff K x ∈ Icc 0 1 :=
  ⟨smoothIndicator_nonneg K (by norm_num) _ x,
    smoothIndicator_le_one K (by norm_num) measurableSet_Icc x⟩

theorem maskedFrequencyCutoff_eq_one (K : ℕ) {x : ℝ} (hx : x ∈ Icc (1 / 2) 2) :
    maskedFrequencyCutoff K x = 1 := by
  rw [maskedFrequencyCutoff, smoothIndicator, convolution_eq_swap]
  calc
    _ = ∫ t : ℝ, scaledExplicitBump K (1 / 8) t := by
      apply integral_congr_ae
      filter_upwards [] with t
      by_cases ht : 1 / 8 < |t|
      · simp only [ContinuousLinearMap.mul_apply',
          scaledExplicitBump_eq_zero_of_scale_lt_abs K (by norm_num) ht, mul_zero]
      · have ht' := abs_le.mp (le_of_not_gt ht)
        have hmem : x - t ∈ Icc (3 / 8 : ℝ) 3 := by
          constructor <;> linarith [hx.1, hx.2, ht'.1, ht'.2]
        simp only [ContinuousLinearMap.mul_apply', indicator_of_mem hmem, one_mul]
    _ = 1 := integral_scaledExplicitBump K (by norm_num)

theorem maskedFrequencyCutoff_eq_zero (K : ℕ) {x : ℝ} (hx : x ∉ Icc (1 / 4) 4) :
    maskedFrequencyCutoff K x = 0 := by
  rw [maskedFrequencyCutoff, smoothIndicator, convolution_eq_swap]
  apply integral_eq_zero_of_ae
  filter_upwards [] with t
  by_cases ht : 1 / 8 < |t|
  · simp only [ContinuousLinearMap.mul_apply',
      scaledExplicitBump_eq_zero_of_scale_lt_abs K (by norm_num) ht, mul_zero, Pi.zero_apply]
  · have ht' := abs_le.mp (le_of_not_gt ht)
    have hnot : x - t ∉ Icc (3 / 8 : ℝ) 3 := by
      intro hmem
      apply hx
      constructor <;> linarith [hmem.1, hmem.2, ht'.1, ht'.2]
    simp only [ContinuousLinearMap.mul_apply', indicator_of_notMem hnot, zero_mul, Pi.zero_apply]

theorem hasCompactSupport_maskedFrequencyCutoff (K : ℕ) :
    HasCompactSupport (maskedFrequencyCutoff K) :=
  HasCompactSupport.intro isCompact_Icc fun _ hx ↦ maskedFrequencyCutoff_eq_zero K hx

/-- The literal source cutoff obeys its factorial derivative bound through order `K`. -/
theorem norm_iteratedDeriv_maskedFrequencyCutoff_le (K k : ℕ) (hk : k ≤ K) (x : ℝ) :
    ‖iteratedDeriv k (maskedFrequencyCutoff K) x‖ ≤
      (14 : ℝ) ^ k * (k.factorial : ℝ) ^ (2 : ℕ) := by
  have h := norm_iteratedDeriv_smoothIndicator_le_explicit K k hk
    (S := Icc (3 / 8 : ℝ) 3) (by norm_num : (0 : ℝ) < 1 / 8) measurableSet_Icc x
  have hπ : 8 * (Real.pi ^ (2 : ℕ) / 6) ≤ (14 : ℝ) := by
    nlinarith [Real.pi_lt_d2, Real.pi_pos]
  calc
    _ ≤ (8 : ℝ) ^ k * ((Real.pi ^ 2 / 6) ^ k * (k.factorial : ℝ) ^ 2) := by
      simpa only [maskedFrequencyCutoff, one_div, inv_inv] using h
    _ = (8 * (Real.pi ^ (2 : ℕ) / 6)) ^ k * (k.factorial : ℝ) ^ 2 := by
      rw [mul_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hπ k) (sq_nonneg _)

/-- The literal dyadic average in the source, using angular frequency. -/
def dyadicFrequencyAverage (K v : ℕ) (f : ℝ → ℝ) : ℝ :=
  ((2 : ℝ) ^ v)⁻¹ * ∫ r in Ioi 0, maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) * f r

theorem dyadicFrequencyAverage_nonneg (K v : ℕ) {f : ℝ → ℝ}
    (hf : ∀ r ∈ Ioi 0, 0 ≤ f r) : 0 ≤ dyadicFrequencyAverage K v f := by
  apply mul_nonneg (by positivity)
  apply setIntegral_nonneg measurableSet_Ioi
  intro r hr
  exact mul_nonneg (maskedFrequencyCutoff_mem_Icc K _).1 (hf r hr)

/-- The actual cutoff-weighted integrand is integrable for a locally bounded Borel function. -/
theorem integrable_maskedFrequencyCutoff_mul (K v : ℕ) {f : ℝ → ℝ}
    (hf : Measurable f) {B : ℝ}
    (hB : ∀ r ∈ Icc 0 (4 * (2 : ℝ) ^ v), |f r| ≤ B) :
    Integrable (fun r ↦ maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) * f r) := by
  have hs : (0 : ℝ) < (2 : ℝ) ^ v := by positivity
  have hBi : Integrable ((Icc 0 (4 * (2 : ℝ) ^ v)).indicator (fun _ ↦ B)) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const isCompact_Icc.measure_ne_top
  apply hBi.mono ?_ ?_
  · exact (((contDiff_maskedFrequencyCutoff K).continuous.measurable.comp
      (measurable_id.div_const _)).mul hf).aestronglyMeasurable
  · filter_upwards [] with r
    by_cases hr : r ∈ Icc 0 (4 * (2 : ℝ) ^ v)
    · rw [indicator_of_mem hr, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (maskedFrequencyCutoff_mem_Icc K _).1]
      exact (mul_le_mul_of_nonneg_right (maskedFrequencyCutoff_mem_Icc K _).2
        (abs_nonneg _)).trans (by simpa using (hB r hr).trans (le_abs_self B))
    · have hnot : r / (2 : ℝ) ^ v ∉ Icc (1 / 4) 4 := by
        intro hmem
        apply hr
        constructor
        · have := (le_div_iff₀ hs).1 hmem.1
          linarith
        · exact (div_le_iff₀ hs).1 hmem.2
      simp [maskedFrequencyCutoff_eq_zero K hnot, indicator_of_notMem hr]

/-- The source's dyadic average of `r²` has the stated exact constant 64. -/
theorem dyadicFrequencyAverage_sq_le (K v : ℕ) :
    dyadicFrequencyAverage K v (fun r ↦ r ^ (2 : ℕ)) ≤ 64 * (4 : ℝ) ^ v := by
  have hs : (0 : ℝ) < (2 : ℝ) ^ v := by positivity
  have hsq : ∀ r ∈ Icc 0 (4 * (2 : ℝ) ^ v), |r ^ (2 : ℕ)| ≤ 16 * ((2 : ℝ) ^ v) ^ 2 := by
    intro r hr
    rw [abs_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ (4 * (2 : ℝ) ^ v) ^ 2 := pow_le_pow_left₀ hr.1 hr.2 2
      _ = _ := by ring
  have hi := integrable_maskedFrequencyCutoff_mul K v (measurable_id.pow_const 2) hsq
  have hconst : Integrable ((Icc 0 (4 * (2 : ℝ) ^ v)).indicator
      (fun _ ↦ 16 * ((2 : ℝ) ^ v) ^ 2)) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const isCompact_Icc.measure_ne_top
  have hpoint : ∀ r : ℝ,
      maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) * r ^ (2 : ℕ) ≤
        (Icc 0 (4 * (2 : ℝ) ^ v)).indicator (fun _ ↦ 16 * ((2 : ℝ) ^ v) ^ 2) r := by
    intro r
    by_cases hr : r ∈ Icc 0 (4 * (2 : ℝ) ^ v)
    · rw [indicator_of_mem hr]
      exact (mul_le_mul_of_nonneg_right (maskedFrequencyCutoff_mem_Icc K _).2
        (sq_nonneg r)).trans (by simpa only [one_mul, abs_of_nonneg (sq_nonneg r)] using hsq r hr)
    · have hnot : r / (2 : ℝ) ^ v ∉ Icc (1 / 4) 4 := by
        intro hmem
        apply hr
        constructor
        · have := (le_div_iff₀ hs).1 hmem.1
          linarith
        · exact (div_le_iff₀ hs).1 hmem.2
      simp [maskedFrequencyCutoff_eq_zero K hnot, indicator_of_notMem hr]
  unfold dyadicFrequencyAverage
  calc
    _ ≤ ((2 : ℝ) ^ v)⁻¹ * ∫ r in Ioi 0,
        (Icc 0 (4 * (2 : ℝ) ^ v)).indicator (fun _ ↦ 16 * ((2 : ℝ) ^ v) ^ 2) r :=
      mul_le_mul_of_nonneg_left (integral_mono hi.integrableOn hconst.integrableOn hpoint)
        (inv_nonneg.mpr hs.le)
    _ ≤ ((2 : ℝ) ^ v)⁻¹ * ∫ r : ℝ,
        (Icc 0 (4 * (2 : ℝ) ^ v)).indicator (fun _ ↦ 16 * ((2 : ℝ) ^ v) ^ 2) r := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hs.le)
      exact setIntegral_le_integral hconst (Eventually.of_forall fun r ↦ by
        by_cases hr : r ∈ Icc 0 (4 * (2 : ℝ) ^ v) <;> simp [hr])
    _ = 64 * (4 : ℝ) ^ v := by
      rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
        Real.volume_real_Icc_of_le (by positivity)]
      simp only [sub_zero]
      have hpow : ((2 : ℝ) ^ v) ^ 2 = (4 : ℝ) ^ v := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]
        norm_num
      field_simp
      nlinarith [hpow]

end FalconerThetaGauge
