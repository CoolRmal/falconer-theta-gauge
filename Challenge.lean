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

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def realGauge (θ r : ℝ) : ℝ := r * Real.exp (-(Real.log (1 / r)) ^ θ)

def thetaGauge (θ : ℝ) (r : ℝ≥0∞) : ℝ≥0∞ :=
  if r < 1 then ENNReal.ofReal (realGauge θ r.toReal) else r

def gaugeMeasure (θ : ℝ) : Measure Plane := Measure.mkMetric (thetaGauge θ)

def distanceSet (E : Set Plane) : Set ℝ :=
  (fun p : Plane × Plane ↦ dist p.1 p.2) '' (E ×ˢ E)

/-- Theorem 1.1: a compact planar set of positive logarithmic-gauge Hausdorff
measure has a distance set of positive Lebesgue measure. -/
theorem theorem_one_one (θ : ℝ) (E : Set Plane)
    (hθ₀ : 2 / 3 < θ) (hθ₁ : θ < 1) (hE : IsCompact E)
    (hGauge : 0 < gaugeMeasure θ E) : 0 < volume (distanceSet E) := by
  sorry

end FalconerThetaGauge
