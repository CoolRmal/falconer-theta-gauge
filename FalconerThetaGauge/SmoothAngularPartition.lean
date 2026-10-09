module

public import FalconerThetaGauge.ExplicitBumpCircle

/-! # Actual convolution partitions of periodic Borel angular cells -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped ContDiff Convolution

namespace FalconerThetaGauge

theorem sum_indicator_partition {ι : Type*} [Fintype ι] (S : ι → Set ℝ)
    (hS : ∀ x : ℝ, ∃! i : ι, x ∈ S i) (x : ℝ) :
    (∑ i : ι, (S i).indicator (fun _ ↦ (1 : ℝ)) x) = 1 := by
  classical
  obtain ⟨i, hi, huniq⟩ := hS x
  rw [sum_eq_single i]
  · exact indicator_of_mem hi _
  · intro j hj hji
    apply indicator_of_notMem
    exact fun hx ↦ hji (huniq j hx)
  · simp

/-- Smoothing an actual finite Borel partition preserves its exact sum one. -/
theorem sum_smoothIndicator_partition {ι : Type*} [Fintype ι] (S : ι → Set ℝ)
    (hSm : ∀ i, MeasurableSet (S i)) (hS : ∀ x : ℝ, ∃! i : ι, x ∈ S i)
    (K : ℕ) {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    (∑ i : ι, smoothIndicator K δ (S i) x) = 1 := by
  classical
  have hi (i : ι) : Integrable (fun t : ℝ ↦ (S i).indicator (fun _ ↦ (1 : ℝ)) t *
      scaledExplicitBump K δ (x - t)) := by
    exact ((hasCompactSupport_scaledExplicitBump K hδ).convolutionExists_right
      (ContinuousLinearMap.mul ℝ ℝ) (locallyIntegrable_indicator_one (hSm i))
      (contDiff_scaledExplicitBump K δ).continuous x).integrable
  simp only [smoothIndicator, convolution_def, ContinuousLinearMap.mul_apply']
  rw [← integral_finsetSum _ (fun i _ ↦ hi i)]
  calc
    _ = ∫ t : ℝ, scaledExplicitBump K δ (x - t) := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [← sum_mul, sum_indicator_partition S hS t, one_mul]
    _ = ∫ t : ℝ, scaledExplicitBump K δ t := integral_sub_left_eq_self _ volume x
    _ = 1 := integral_scaledExplicitBump K hδ

/-- Raw convolution of an angular cell is supported in its actual closed smoothing neighborhood. -/
theorem smoothIndicator_eq_zero_outside_cthickening (K : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (S : Set ℝ) {x : ℝ} (hx : x ∉ Metric.cthickening δ S) :
    smoothIndicator K δ S x = 0 := by
  rw [smoothIndicator, convolution_eq_swap]
  apply integral_eq_zero_of_ae
  filter_upwards [] with t
  by_cases ht : δ < |t|
  · simp only [ContinuousLinearMap.mul_apply',
    scaledExplicitBump_eq_zero_of_scale_lt_abs K hδ ht, mul_zero, Pi.zero_apply]
  · have hnot : x - t ∉ S := by
      intro hmem
      apply hx
      apply Metric.mem_cthickening_of_dist_le x (x - t) δ S hmem
      simpa only [Real.dist_eq, sub_sub_cancel] using le_of_not_gt ht
    simp only [ContinuousLinearMap.mul_apply', indicator_of_notMem hnot, zero_mul, Pi.zero_apply]

theorem tsupport_smoothIndicator_subset_cthickening (K : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (S : Set ℝ) : tsupport (smoothIndicator K δ S) ⊆ Metric.cthickening δ S := by
  apply closure_minimal _ Metric.isClosed_cthickening
  intro x hx
  by_contra h
  exact hx (smoothIndicator_eq_zero_outside_cthickening K hδ S h)

end FalconerThetaGauge
