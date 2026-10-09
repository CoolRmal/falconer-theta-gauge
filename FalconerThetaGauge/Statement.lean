module

public import FalconerThetaGauge.Gauge
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# The geometric objects of Theorem 1.1

`Plane` carries the Euclidean norm. `gaugeMeasure` is Mathlib's arbitrary-gauge
Hausdorff measure, and `distanceSet` is the ordinary unpinned distance set.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FalconerThetaGauge

noncomputable section

/-- The real Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Hausdorff measure with the stretched logarithmic gauge of the manuscript. -/
def gaugeMeasure (θ : ℝ) : Measure Plane := Measure.mkMetric (thetaGauge θ)

/-- The standard countable-cover formula for the gauge Hausdorff measure. -/
theorem gaugeMeasure_apply (θ : ℝ) (E : Set Plane) :
    gaugeMeasure θ E =
      ⨆ (r : ℝ≥0∞) (_ : 0 < r),
        ⨅ (t : ℕ → Set Plane) (_ : E ⊆ Set.iUnion t)
          (_ : ∀ n, Metric.ediam (t n) ≤ r),
          ∑' n, ⨆ _ : (t n).Nonempty, thetaGauge θ (Metric.ediam (t n)) :=
  Measure.mkMetric_apply _ _

/-- The set of all Euclidean distances between two points of `E`. -/
def distanceSet (E : Set Plane) : Set ℝ :=
  (fun p : Plane × Plane ↦ dist p.1 p.2) '' (E ×ˢ E)

theorem mem_distanceSet {E : Set Plane} {r : ℝ} :
    r ∈ distanceSet E ↔ ∃ x ∈ E, ∃ y ∈ E, dist x y = r := by
  simp only [distanceSet, Set.mem_image, Set.mem_prod]
  aesop

theorem distanceSet_nonneg {E : Set Plane} {r : ℝ} (hr : r ∈ distanceSet E) : 0 ≤ r := by
  obtain ⟨x, _, y, _, rfl⟩ := mem_distanceSet.mp hr
  exact dist_nonneg

theorem zero_mem_distanceSet {E : Set Plane} (hE : E.Nonempty) : 0 ∈ distanceSet E := by
  obtain ⟨x, hx⟩ := hE
  exact mem_distanceSet.mpr ⟨x, hx, x, hx, dist_self x⟩

theorem isCompact_distanceSet {E : Set Plane} (hE : IsCompact E) :
    IsCompact (distanceSet E) := by
  exact (hE.prod hE).image continuous_dist

theorem measurableSet_distanceSet {E : Set Plane} (hE : IsCompact E) :
    MeasurableSet (distanceSet E) := (isCompact_distanceSet hE).measurableSet

theorem gaugeMeasure_le_hausdorffMeasure_one (θ : ℝ) :
    gaugeMeasure θ ≤ Measure.hausdorffMeasure 1 := by
  simpa [gaugeMeasure, Measure.hausdorffMeasure] using
    (Measure.mkMetric_mono (X := Plane) (Filter.Eventually.of_forall (thetaGauge_le θ)))

@[simp]
theorem gaugeMeasure_singleton (θ : ℝ) (x : Plane) : gaugeMeasure θ {x} = 0 := by
  have := Measure.nullSingletonClass_hausdorff Plane (by norm_num : (0 : ℝ) < 1)
  exact le_antisymm ((gaugeMeasure_le_hausdorffMeasure_one θ {x}).trans (by simp)) bot_le

instance nullSingletonClass_gaugeMeasure (θ : ℝ) : NullSingletonClass (gaugeMeasure θ) :=
  ⟨gaugeMeasure_singleton θ⟩

theorem gaugeMeasure_countable (θ : ℝ) {E : Set Plane} (hE : E.Countable) :
    gaugeMeasure θ E = 0 := hE.measure_zero _

theorem not_countable_of_gaugeMeasure_pos {θ : ℝ} {E : Set Plane}
    (hE : 0 < gaugeMeasure θ E) : ¬E.Countable := by
  intro hcount
  simp [gaugeMeasure_countable θ hcount] at hE

theorem nontrivial_of_gaugeMeasure_pos {θ : ℝ} {E : Set Plane}
    (hE : 0 < gaugeMeasure θ E) : E.Nontrivial :=
  Set.not_subsingleton_iff.mp fun hsub ↦ not_countable_of_gaugeMeasure_pos hE hsub.countable

theorem exists_dist_pos_of_gaugeMeasure_pos {θ : ℝ} {E : Set Plane}
    (hE : 0 < gaugeMeasure θ E) : ∃ r ∈ distanceSet E, 0 < r := by
  obtain ⟨x, hx, y, hy, hxy⟩ := nontrivial_of_gaugeMeasure_pos hE
  exact ⟨dist x y, mem_distanceSet.mpr ⟨x, hx, y, hy, rfl⟩, dist_pos.mpr hxy⟩

theorem hausdorffMeasure_one_pos_of_gaugeMeasure_pos {θ : ℝ} {E : Set Plane}
    (hE : 0 < gaugeMeasure θ E) : 0 < Measure.hausdorffMeasure 1 E :=
  hE.trans_le (gaugeMeasure_le_hausdorffMeasure_one θ E)

theorem nonempty_of_gaugeMeasure_pos {θ : ℝ} {E : Set Plane}
    (hE : 0 < gaugeMeasure θ E) : E.Nonempty := by
  by_contra h
  simp [Set.not_nonempty_iff_eq_empty.mp h] at hE

end

end FalconerThetaGauge
