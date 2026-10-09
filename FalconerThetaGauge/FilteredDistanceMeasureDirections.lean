module

public import FalconerThetaGauge.FilteredDistanceMeasureGeometry
public import FalconerThetaGauge.FilteredDistanceMeasureCircle
public import FalconerThetaGauge.RadialProjectionSpread
public import FalconerThetaGauge.OrliczSmallSet

/-!
# Actual bad-direction pairs and their Orlicz mass bound

Bad sets are Borel subsets of the pin/circle product. Their sections are the
actual excluded directions at each pin. This retains the joint measurability
needed for the product measure, rather than postulating a bound on pair mass.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace FalconerThetaGauge

/-- The measurable section of a bad-direction family at a pin. -/
def badDirectionsAt (Z : Set (Plane × UnitCircle)) (x : Plane) : Set UnitCircle :=
  Prod.mk x ⁻¹' Z

theorem measurableSet_badDirectionsAt {Z : Set (Plane × UnitCircle)}
    (hZ : MeasurableSet Z) (x : Plane) : MeasurableSet (badDirectionsAt Z x) :=
  measurable_prodMk_left hZ

/-- Actual pairs whose radial direction from the first coordinate is bad. -/
def radialBadPairs (Z : Set (Plane × UnitCircle)) : Set (Plane × Plane) :=
  (fun p ↦ (p.1, radialProjection p.1 p.2)) ⁻¹' Z

theorem measurableSet_radialBadPairs {Z : Set (Plane × UnitCircle)}
    (hZ : MeasurableSet Z) : MeasurableSet (radialBadPairs Z) :=
  (measurable_fst.prodMk measurable_radialProjection) hZ

/-- The actual pair mass equals the average actual pinned radial pushforward mass. -/
theorem measure_radialBadPairs (μ ν : Measure Plane) [SFinite ν]
    {Z : Set (Plane × UnitCircle)} (hZ : MeasurableSet Z) :
    μ.prod ν (radialBadPairs Z) =
      ∫⁻ x, ν.map (radialProjection x) (badDirectionsAt Z x) ∂μ := by
  rw [Measure.prod_apply (measurableSet_radialBadPairs hZ)]
  apply lintegral_congr
  intro x
  rw [Measure.map_apply measurable_radialProjection.of_uncurry_left
    (measurableSet_badDirectionsAt hZ x)]
  rfl

/-- The explicit per-pin eighth-order filtering cost from Lemma 6.13. -/
def radialFilterCost (N : ℕ) (E : ℝ) (K : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (3 * (N + 1) * (2 : ℝ) ^ (-E)) +
    ENNReal.ofReal ((2 : ℝ) ^ 8 * E ^ (-8 : ℝ)) * K

/-- Short Borel direction sets have the paper's actual small pair mass,
using the prepared densities and a common eighth-order Orlicz bound. -/
theorem measure_radialBadPairs_le_filterCost
    (μ ν : Measure Plane) [IsProbabilityMeasure μ] [IsFiniteMeasure ν]
    {S : Set Plane} (hS : MeasurableSet S) (hμ : μ S = 1)
    {Z : Set (Plane × UnitCircle)} (hZ : MeasurableSet Z)
    (N : ℕ) {E : ℝ} (hE : 0 < E)
    (hbudget : Real.log (2 * Real.pi * ((N : ℝ) ^ 2 + 1)) ≤
      (2 * Real.log 2 - 1) * E) {K : ℝ≥0∞}
    (hpin : ∀ x ∈ S,
      circleArcLength.withDensity (radialProjectionDensity ν x) = ν.map (radialProjection x) ∧
      radialOrliczMoment ν 8 x ≤ K)
    (hlength : ∀ x ∈ S,
      circleArcLength (badDirectionsAt Z x) ≤ ENNReal.ofReal (filterBadDirectionLength N E)) :
    μ.prod ν (radialBadPairs Z) ≤ radialFilterCost N E K := by
  rw [measure_radialBadPairs μ ν hZ]
  have hcarrier : ∀ᵐ x ∂μ, x ∈ S :=
    (ae_mem_iff_measure_eq hS.nullMeasurableSet).2 (by simpa using hμ)
  have hpoint : ∀ᵐ x ∂μ,
      ν.map (radialProjection x) (badDirectionsAt Z x) ≤ radialFilterCost N E K := by
    filter_upwards [hcarrier] with x hx
    rw [← (hpin x hx).1]
    exact withDensity_filter_bad_directions_of_budget circleArcLength N hE hbudget
      (hpin x hx).2 (measurableSet_badDirectionsAt hZ x) (hlength x hx)
  simpa using lintegral_mono_ae hpoint

/-- Each test family is symmetric in its direction variable, exactly as in Lemma 6.4. -/
def IsSymmetricBadDirections (Z : Set (Plane × UnitCircle)) : Prop :=
  ∀ x w, (x, circleAntipode w) ∈ Z ↔ (x, w) ∈ Z

/-- Pairs excluded by the manuscript's direction `e(x,y)` at the first pin. -/
def leftBadPairs (Z : Set (Plane × UnitCircle)) : Set (Plane × Plane) :=
  (fun p ↦ (p.1, pairDirection p.1 p.2)) ⁻¹' Z

theorem measurableSet_leftBadPairs {Z : Set (Plane × UnitCircle)}
    (hZ : MeasurableSet Z) : MeasurableSet (leftBadPairs Z) :=
  (measurable_fst.prodMk measurable_pairDirection) hZ

/-- Direction reversal is accounted for on the separated pairs, rather than
assuming that `e(x,y)` equals the outgoing radial direction. -/
theorem measure_leftBadPairs_eq_radialBadPairs (μ ν : Measure Plane)
    {Z : Set (Plane × UnitCircle)} (hsym : IsSymmetricBadDirections Z)
    (hne : ∀ᵐ p ∂μ.prod ν, p.1 ≠ p.2) :
    μ.prod ν (leftBadPairs Z) = μ.prod ν (radialBadPairs Z) := by
  apply measure_congr
  filter_upwards [hne] with p hp
  apply propext
  change (p.1, pairDirection p.1 p.2) ∈ Z ↔ (p.1, radialProjection p.1 p.2) ∈ Z
  rw [pairDirection_eq_circleAntipode_radialProjection hp]
  exact hsym p.1 (radialProjection p.1 p.2)

/-- At the second pin the manuscript's `e(x,y)` already is the outgoing radial direction. -/
def rightBadPairs (Z : Set (Plane × UnitCircle)) : Set (Plane × Plane) :=
  Prod.swap ⁻¹' radialBadPairs Z

theorem measurableSet_rightBadPairs {Z : Set (Plane × UnitCircle)}
    (hZ : MeasurableSet Z) : MeasurableSet (rightBadPairs Z) :=
  measurable_swap (measurableSet_radialBadPairs hZ)

theorem measure_rightBadPairs (μ ν : Measure Plane) [SFinite μ] [SFinite ν]
    {Z : Set (Plane × UnitCircle)} (hZ : MeasurableSet Z) :
    μ.prod ν (rightBadPairs Z) = ν.prod μ (radialBadPairs Z) := by
  rw [rightBadPairs, ← Measure.map_apply measurable_swap (measurableSet_radialBadPairs hZ),
    Measure.prod_swap]

end FalconerThetaGauge
