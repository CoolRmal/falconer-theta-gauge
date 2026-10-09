module

public import FalconerThetaGauge.ExplicitBumpCutoff

/-! # Periodicity and antipodal symmetry of the actual smooth masks -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff Convolution

namespace FalconerThetaGauge

theorem image_translate_eq_of_periodic_set {Z : Set ℝ} {p : ℝ}
    (hZ : ∀ x, x + p ∈ Z ↔ x ∈ Z) : (fun x : ℝ ↦ x + p) '' Z = Z := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hZ y).mpr hy
  · intro hx
    refine ⟨x - p, ?_, sub_add_cancel _ _⟩
    exact (hZ (x - p)).mp (by simpa only [sub_add_cancel] using hx)

theorem cthickening_periodic_set {Z : Set ℝ} {p δ : ℝ}
    (hZ : ∀ x, x + p ∈ Z ↔ x ∈ Z) (x : ℝ) :
    x + p ∈ Metric.cthickening δ Z ↔ x ∈ Metric.cthickening δ Z := by
  have hi := Metric.infEDist_image (x := x) (t := Z) (isometry_add_right p)
  rw [image_translate_eq_of_periodic_set hZ] at hi
  simp only [Metric.mem_cthickening_iff, hi]

theorem smoothIndicator_periodic (K : ℕ) (δ : ℝ) {S : Set ℝ} {p : ℝ}
    (hS : ∀ x, x + p ∈ S ↔ x ∈ S) : Periodic (smoothIndicator K δ S) p := by
  intro x
  rw [smoothIndicator, convolution_eq_swap, convolution_eq_swap]
  apply integral_congr_ae
  filter_upwards [] with t
  have heq : x + p - t = (x - t) + p := by ring
  simp only [ContinuousLinearMap.mul_apply', heq]
  by_cases ht : x - t ∈ S
  · simp only [indicator_of_mem ht, indicator_of_mem ((hS _).mpr ht)]
  · simp only [indicator_of_notMem ht, indicator_of_notMem (mt (hS _).mp ht)]

/-- Shift by `π` is exactly antipodal evenness when this angular mask descends to the circle. -/
theorem explicitPassingMask_periodic (K : ℕ) (δ : ℝ) {Z : Set ℝ} {p : ℝ}
    (hZ : ∀ x, x + p ∈ Z ↔ x ∈ Z) : Periodic (explicitPassingMask K δ Z) p :=
  smoothIndicator_periodic K δ (cthickening_periodic_set hZ)

theorem image_neg_eq_of_symmetric_set {Z : Set ℝ}
    (hZ : ∀ x, -x ∈ Z ↔ x ∈ Z) : (fun x : ℝ ↦ -x) '' Z = Z := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hZ y).mpr hy
  · intro hx
    exact ⟨-x, (hZ x).mpr hx, neg_neg x⟩

theorem cthickening_symmetric_set {Z : Set ℝ} {δ : ℝ}
    (hZ : ∀ x, -x ∈ Z ↔ x ∈ Z) (x : ℝ) :
    -x ∈ Metric.cthickening δ Z ↔ x ∈ Metric.cthickening δ Z := by
  have hi := Metric.infEDist_image (x := x) (t := Z) (IsometryEquiv.neg ℝ).isometry
  simp only [IsometryEquiv.neg_apply] at hi
  rw [image_neg_eq_of_symmetric_set hZ] at hi
  simp only [Metric.mem_cthickening_iff, hi]

theorem smoothIndicator_even (K : ℕ) (δ : ℝ) {S : Set ℝ}
    (hS : ∀ x, -x ∈ S ↔ x ∈ S) (x : ℝ) :
    smoothIndicator K δ S (-x) = smoothIndicator K δ S x := by
  rw [smoothIndicator, convolution_eq_swap, convolution_eq_swap]
  rw [← integral_neg_eq_self _ volume]
  apply integral_congr_ae
  filter_upwards [] with t
  have heq : -x - -t = -(x - t) := by ring
  simp only [ContinuousLinearMap.mul_apply', heq, scaledExplicitBump_even]
  by_cases ht : x - t ∈ S
  · simp only [indicator_of_mem ht, indicator_of_mem ((hS _).mpr ht)]
  · simp only [indicator_of_notMem ht, indicator_of_notMem (mt (hS _).mp ht)]

theorem explicitPassingMask_even (K : ℕ) (δ : ℝ) {Z : Set ℝ}
    (hZ : ∀ x, -x ∈ Z ↔ x ∈ Z) (x : ℝ) :
    explicitPassingMask K δ Z (-x) = explicitPassingMask K δ Z x :=
  smoothIndicator_even K δ (cthickening_symmetric_set hZ) x

end FalconerThetaGauge
