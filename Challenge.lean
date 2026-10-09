module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Independent specification of Theorem 1.1

Source: `docs/falconer-theta-gauge-proof.pdf`, pages 2--3.
This specification imports only Mathlib. All custom definitions are repeated
independently, and the sole deliberate theorem hole is the comparator target.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace FalconerThetaGauge

/-- The real plane with its Euclidean metric. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The manuscript's gauge expression, prescribed for `0 < r < 1` and zero at `r = 0`. -/
def realGauge (θ r : ℝ) : ℝ := r * Real.exp (-(Real.log (1 / r)) ^ θ)

/-- The gauge on extended nonnegative radii, extended by the identity for `r ≥ 1`.
Hausdorff measure depends only on the values at arbitrarily small radii. -/
def thetaGauge (θ : ℝ) (r : ℝ≥0∞) : ℝ≥0∞ :=
  if r < 1 then ENNReal.ofReal (realGauge θ r.toReal) else r

/-- Gauge Hausdorff measure from countable covers weighted by their Euclidean diameters. -/
def gaugeMeasure (θ : ℝ) : Measure Plane := Measure.mkMetric (thetaGauge θ)

/-- All Euclidean distances between pairs of points of `E`, as a subset of the real line. -/
def distanceSet (E : Set Plane) : Set ℝ :=
  (fun p : Plane × Plane ↦ dist p.1 p.2) '' (E ×ˢ E)

/-- Theorem 1.1: a compact planar set of positive logarithmic-gauge Hausdorff
measure has a distance set of positive Lebesgue measure. -/
theorem theorem_one_one (θ : ℝ) (E : Set Plane)
    (hθ₀ : 2 / 3 < θ) (hθ₁ : θ < 1) (hE : IsCompact E)
    (hGauge : 0 < gaugeMeasure θ E) : 0 < volume (distanceSet E) := by
  sorry

end FalconerThetaGauge
