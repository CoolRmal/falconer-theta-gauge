module

public import FalconerThetaGauge.SeparatedDirectionsNeighborhood
public import FalconerThetaGauge.DirectionalTestsMaskSupport
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-! # The literal localized angular cutoff from source Section 3.3 -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff

namespace FalconerThetaGauge

/-- The actual finite-order smooth probability convolution from Section 3.3:
smooth the `0.15` neighborhood of the common oriented arc at radius `1/20`. -/
def preparedArcCutoff (K : ℕ) (α : ℝ) : UnitCircle → ℝ :=
  circlePassingMask K (1 / 20)
    (closedArcNeighborhood (1 / 10) (closedDirectionArc α (1 / 40)))

theorem preparedArcCutoff_comp_angle (K : ℕ) (α : ℝ) :
    (fun θ ↦ preparedArcCutoff K α (unitCircleOfAngle θ)) =
      smoothIndicator K (1 / 20)
        (Metric.cthickening (3 / 20) (angularPassingSet (closedDirectionArc α (1 / 40)))) := by
  ext θ
  rw [preparedArcCutoff, circlePassingMask_comp_angle, explicitPassingMask,
    angularPassingSet_closedArcNeighborhood, cthickening_cthickening
      (by norm_num : (0 : ℝ) ≤ 1 / 20) (by norm_num : (0 : ℝ) ≤ 1 / 10)]
  norm_num

@[fun_prop]
theorem measurable_preparedArcCutoff (K : ℕ) (α : ℝ) :
    Measurable (preparedArcCutoff K α) :=
  measurable_circlePassingMask K (by norm_num) _

theorem preparedArcCutoff_mem_Icc (K : ℕ) (α : ℝ) (w : UnitCircle) :
    preparedArcCutoff K α w ∈ Icc 0 1 :=
  circlePassingMask_mem_Icc K (by norm_num) _ _

theorem contDiff_preparedArcCutoff_comp_angle (K : ℕ) (α : ℝ) :
    ContDiff ℝ ∞ (fun θ ↦ preparedArcCutoff K α (unitCircleOfAngle θ)) :=
  contDiff_circlePassingMask_comp_angle K (by norm_num) _

theorem preparedArcCutoff_eq_one (K : ℕ) (α : ℝ) {w : UnitCircle}
    (hw : w ∈ closedArcNeighborhood (1 / 10) (closedDirectionArc α (1 / 40))) :
    preparedArcCutoff K α w = 1 :=
  circlePassingMask_eq_one K (by norm_num) hw

/-- The actual localized cutoff is identically one at every true pair direction
from the prepared support discs. -/
theorem preparedArcCutoff_pairDirection_eq_one (K : ℕ) {a b x y : Plane}
    (hab : dist a b = 1 / 4) (hx : x ∈ Metric.ball a (1 / 400))
    (hy : y ∈ Metric.ball b (1 / 400)) :
    preparedArcCutoff K (radialAngle b a) (pairDirection x y) = 1 :=
  preparedArcCutoff_eq_one K _ (self_subset_closedArcNeighborhood _ _
    (prepared_pairDirection_mem_closedDirectionArc hab hx hy))

theorem preparedArcCutoff_eq_zero (K : ℕ) (α : ℝ) {w : UnitCircle}
    (hw : w ∉ closedArcNeighborhood (1 / 5) (closedDirectionArc α (1 / 40))) :
    preparedArcCutoff K α w = 0 := by
  apply circlePassingMask_eq_zero K (by norm_num)
  intro h
  apply hw
  have h' := closedArcNeighborhood_closedArcNeighborhood_subset
    (by norm_num : (0 : ℝ) ≤ 2 * (1 / 20))
    (by norm_num : (0 : ℝ) ≤ 1 / 10) (closedDirectionArc α (1 / 40)) h
  norm_num at h' ⊢
  exact h'

/-- The localized symbol vanishes throughout the literal `π/3` neighborhood
of the opposite arc, as required by the source circular stationary phase lemma. -/
theorem preparedArcCutoff_eq_zero_on_opposite (K : ℕ) (α : ℝ) {w : UnitCircle}
    (hw : w ∈ closedArcNeighborhood (Real.pi / 3)
      (circleAntipode '' closedDirectionArc α (1 / 40))) :
    preparedArcCutoff K α w = 0 := by
  apply preparedArcCutoff_eq_zero
  exact fun h ↦ Set.disjoint_left.mp (prepared_arc_neighborhood_disjoint_opposite α) h hw

/-- Every angular derivative also vanishes there, including boundary points of
the opposite closed neighborhood. -/
theorem iteratedDeriv_preparedArcCutoff_eq_zero_on_opposite (K k : ℕ) (α : ℝ) {θ : ℝ}
    (hθ : unitCircleOfAngle θ ∈ closedArcNeighborhood (Real.pi / 3)
      (circleAntipode '' closedDirectionArc α (1 / 40))) :
    iteratedDeriv k (fun t ↦ preparedArcCutoff K α (unitCircleOfAngle t)) θ = 0 := by
  apply iteratedDeriv_circlePassingMask_eq_zero K k (by norm_num : (0 : ℝ) < 1 / 20)
  intro h
  have h' := closedArcNeighborhood_closedArcNeighborhood_subset
    (by norm_num : (0 : ℝ) ≤ 2 * (1 / 20))
    (by norm_num : (0 : ℝ) ≤ 1 / 10) (closedDirectionArc α (1 / 40)) h
  norm_num at h'
  exact Set.disjoint_left.mp (prepared_arc_neighborhood_disjoint_opposite α) h' hθ

/-- The actual source derivative constant, with the checked `π < 3.1416` bound. -/
theorem norm_iteratedDeriv_preparedArcCutoff_le (K k : ℕ) (hk : k ≤ K)
    (α θ : ℝ) :
    ‖iteratedDeriv k (fun t ↦ preparedArcCutoff K α (unitCircleOfAngle t)) θ‖ ≤
      (33 : ℝ) ^ k * (k.factorial : ℝ) ^ 2 := by
  have heq : (fun t ↦ preparedArcCutoff K α (unitCircleOfAngle t)) =
      explicitPassingMask K (1 / 20)
        (angularPassingSet (closedArcNeighborhood (1 / 10) (closedDirectionArc α (1 / 40)))) :=
    funext (circlePassingMask_comp_angle K (1 / 20) _)
  rw [heq]
  have hbase : (20 : ℝ) * (Real.pi ^ 2 / 6) ≤ 33 := by
    have hs := mul_self_lt_mul_self Real.pi_pos.le Real.pi_lt_d4
    nlinarith
  calc
    _ ≤ (1 / 20 : ℝ)⁻¹ ^ k * ((Real.pi ^ 2 / 6) ^ k * (k.factorial : ℝ) ^ 2) :=
      norm_iteratedDeriv_explicitPassingMask_le K k hk (by norm_num) _ θ
    _ = (20 * (Real.pi ^ 2 / 6)) ^ k * (k.factorial : ℝ) ^ 2 := by
      norm_num only [inv_div, one_div_one, mul_one]
      rw [← mul_assoc, ← mul_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) hbase k) (by positivity)

end FalconerThetaGauge
