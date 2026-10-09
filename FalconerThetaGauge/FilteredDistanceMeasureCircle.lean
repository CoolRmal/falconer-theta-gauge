module

public import FalconerThetaGauge.RadialProjectionDefinitions

/-!
# The actual circle antipode and the manuscript's direction reversal
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace FalconerThetaGauge

/-- The true antipodal map of the Euclidean unit circle. -/
def circleAntipode (w : UnitCircle) : UnitCircle := ⟨-(w : Plane), by simp⟩

@[simp]
theorem coe_circleAntipode (w : UnitCircle) :
    (circleAntipode w : Plane) = -(w : Plane) := rfl

@[fun_prop]
theorem continuous_circleAntipode : Continuous circleAntipode := by
  unfold circleAntipode
  fun_prop

theorem pairDirection_eq_circleAntipode_radialProjection {x y : Plane} (hxy : x ≠ y) :
    pairDirection x y = circleAntipode (radialProjection x y) := by
  apply Subtype.ext
  rw [coe_pairDirection_of_ne hxy, coe_circleAntipode, coe_radialProjection_of_ne hxy,
    norm_sub_rev, ← smul_neg, neg_sub]

end FalconerThetaGauge
