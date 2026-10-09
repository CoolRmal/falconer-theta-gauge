/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.ExplicitBumpCutoff
public import FalconerThetaGauge.ExplicitBumpPeriodic

/-! # The literal quantitative cutoff at a circular stationary point -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff Convolution

namespace FalconerThetaGauge

/-- Convolve the interval `[-π/4,π/4]` with the order-`K` kernel of radius `π/12`. -/
def circularStationaryCutoff (K : ℕ) : ℝ → ℝ :=
  smoothIndicator K (Real.pi / 12) (Icc (-(Real.pi / 4)) (Real.pi / 4))

theorem contDiff_circularStationaryCutoff (K : ℕ) :
    ContDiff ℝ ∞ (circularStationaryCutoff K) :=
  contDiff_smoothIndicator K (by positivity) measurableSet_Icc

theorem circularStationaryCutoff_mem_Icc (K : ℕ) (x : ℝ) :
    circularStationaryCutoff K x ∈ Icc 0 1 :=
  ⟨smoothIndicator_nonneg K (by positivity) _ x,
    smoothIndicator_le_one K (by positivity) measurableSet_Icc x⟩

theorem circularStationaryCutoff_even (K : ℕ) (x : ℝ) :
    circularStationaryCutoff K (-x) = circularStationaryCutoff K x := by
  apply smoothIndicator_even
  intro y
  simp only [mem_Icc]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem circularStationaryCutoff_eq_one (K : ℕ) {x : ℝ} (hx : |x| ≤ Real.pi / 6) :
    circularStationaryCutoff K x = 1 := by
  rw [circularStationaryCutoff, smoothIndicator, convolution_eq_swap]
  calc
    _ = ∫ t : ℝ, scaledExplicitBump K (Real.pi / 12) t := by
      apply integral_congr_ae
      filter_upwards [] with t
      by_cases ht : Real.pi / 12 < |t|
      · simp only [ContinuousLinearMap.mul_apply',
          scaledExplicitBump_eq_zero_of_scale_lt_abs K (by positivity) ht, mul_zero]
      · have hmem : x - t ∈ Icc (-(Real.pi / 4)) (Real.pi / 4) := by
          have hxb := abs_le.mp hx
          have htb := abs_le.mp (le_of_not_gt ht)
          constructor <;> linarith [hxb.1, hxb.2, htb.1, htb.2]
        simp only [ContinuousLinearMap.mul_apply', indicator_of_mem hmem, one_mul]
    _ = 1 := integral_scaledExplicitBump K (by positivity)

theorem circularStationaryCutoff_eq_zero (K : ℕ) {x : ℝ} (hx : Real.pi / 3 < |x|) :
    circularStationaryCutoff K x = 0 := by
  rw [circularStationaryCutoff, smoothIndicator, convolution_eq_swap]
  apply integral_eq_zero_of_ae
  filter_upwards [] with t
  by_cases ht : Real.pi / 12 < |t|
  · simp only [ContinuousLinearMap.mul_apply',
      scaledExplicitBump_eq_zero_of_scale_lt_abs K (by positivity) ht, mul_zero, Pi.zero_apply]
  · have hnot : x - t ∉ Icc (-(Real.pi / 4)) (Real.pi / 4) := by
      intro hmem
      have htb := abs_le.mp (le_of_not_gt ht)
      have hxb : |x| ≤ Real.pi / 3 := abs_le.mpr
        ⟨by linarith [hmem.1, htb.1], by linarith [hmem.2, htb.2]⟩
      exact hx.not_ge hxb
    simp only [ContinuousLinearMap.mul_apply', indicator_of_notMem hnot, zero_mul, Pi.zero_apply]

theorem support_circularStationaryCutoff_subset (K : ℕ) :
    support (circularStationaryCutoff K) ⊆ Icc (-(Real.pi / 3)) (Real.pi / 3) := by
  intro x hx
  apply abs_le.mp
  by_contra h
  exact mem_support.mp hx (circularStationaryCutoff_eq_zero K (lt_of_not_ge h))

theorem hasCompactSupport_circularStationaryCutoff (K : ℕ) :
    HasCompactSupport (circularStationaryCutoff K) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (support_circularStationaryCutoff_subset K)

theorem norm_iteratedDeriv_circularStationaryCutoff_le (K k : ℕ) (hk : k ≤ K) (x : ℝ) :
    ‖iteratedDeriv k (circularStationaryCutoff K) x‖ ≤
      (2 * Real.pi) ^ k * (k.factorial : ℝ) ^ 2 := by
  have h := norm_iteratedDeriv_smoothIndicator_le_explicit K k hk
    (S := Icc (-(Real.pi / 4)) (Real.pi / 4))
    (by positivity : 0 < Real.pi / 12) measurableSet_Icc x
  change ‖iteratedDeriv k (circularStationaryCutoff K) x‖ ≤ _ at h
  convert h using 1
  rw [← mul_assoc, ← mul_pow]
  have hbase : (Real.pi / 12)⁻¹ * (Real.pi ^ 2 / 6) = 2 * Real.pi := by
    field_simp
    ring
  rw [hbase]

end FalconerThetaGauge
