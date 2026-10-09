module

public import FalconerThetaGauge.DirectionalTestsTube

/-! # The literal projection coincidence count of the normalized anchor restriction -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- The actual probability restricted and normalized to the occupied anchor cell. -/
def projectionAnchorMeasure (ρ : Measure Plane) (p : ℕ) (P : Fin 2 → ℤ) : Measure Plane :=
  normalizedRestrict ρ (dyadicCube p P)

instance (ρ : Measure Plane) [SFinite ρ] (p : ℕ) (P : Fin 2 → ℤ) :
    SFinite (projectionAnchorMeasure ρ p P) := by
  unfold projectionAnchorMeasure normalizedRestrict
  infer_instance

theorem isProbabilityMeasure_projectionAnchorMeasure (ρ : Measure Plane)
    [IsFiniteMeasure ρ] (p : ℕ) (P : Fin 2 → ℤ) (hP : 0 < unitCellWeight ρ p P) :
    IsProbabilityMeasure (projectionAnchorMeasure ρ p P) := by
  have hp : 0 < ρ (dyadicCube p P) :=
    (ENNReal.toReal_pos_iff.mp hP).1
  exact isProbabilityMeasure_normalizedRestrict hp.ne' (measure_ne_top ρ _)

/-- The actual closed pair-coincidence set at generation `u`; `E=εN`. -/
def projectionCoincidenceSet (u : ℕ) (E width : ℝ) (w : UnitCircle) : Set (Plane × Plane) :=
  {z | |inner ℝ (z.1 - z.2) (w : Plane)| ≤
    width * (2 : ℝ) ^ (-(u : ℝ)) * (2 : ℝ) ^ (2 * E)}

theorem measurableSet_projectionCoincidenceRelation (u : ℕ) (E width : ℝ) :
    MeasurableSet {p : UnitCircle × (Plane × Plane) |
      p.2 ∈ projectionCoincidenceSet u E width p.1} := by
  change MeasurableSet {p : UnitCircle × (Plane × Plane) |
    |inner ℝ (p.2.1 - p.2.2) (p.1 : Plane)| ≤
      width * (2 : ℝ) ^ (-(u : ℝ)) * (2 : ℝ) ^ (2 * E)}
  apply (isClosed_le _ continuous_const).measurableSet
  change Continuous (fun p : UnitCircle × (Plane × Plane) ↦
    |inner ℝ (p.2.1 - p.2.2) (p.1 : Plane)|)
  fun_prop

/-- The literal pair-probability count `Πᵘ` for any given actual anchor measure. -/
def projectionCountOfMeasure (ν : Measure Plane) (u : ℕ) (E width : ℝ)
    (w : UnitCircle) : ℝ := (ν.prod ν).real (projectionCoincidenceSet u E width w)

theorem measurable_projectionCountOfMeasure (ν : Measure Plane) [SFinite ν]
    (u : ℕ) (E width : ℝ) : Measurable (projectionCountOfMeasure ν u E width) := by
  have hm := (measurable_measure_prodMk_left (ν := ν.prod ν)
    (measurableSet_projectionCoincidenceRelation u E width)).ennreal_toReal
  exact hm

theorem projectionCountOfMeasure_nonneg (ν : Measure Plane) (u : ℕ) (E width : ℝ)
    (w : UnitCircle) : 0 ≤ projectionCountOfMeasure ν u E width w := measureReal_nonneg

theorem projectionCountOfMeasure_le_one (ν : Measure Plane) [IsProbabilityMeasure ν]
    (u : ℕ) (E width : ℝ) (w : UnitCircle) : projectionCountOfMeasure ν u E width w ≤ 1 :=
  measureReal_le_one

theorem integrable_projectionCountOfMeasure (ν : Measure Plane) [IsProbabilityMeasure ν]
    (u : ℕ) (E width : ℝ) : Integrable (projectionCountOfMeasure ν u E width) circleArcLength :=
  Integrable.of_bound (measurable_projectionCountOfMeasure ν u E width).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun w ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (projectionCountOfMeasure_nonneg ν u E width w)]
      exact projectionCountOfMeasure_le_one ν u E width w))

theorem projectionCountOfMeasure_antipodal (ν : Measure Plane) (u : ℕ) (E width : ℝ)
    (w : UnitCircle) : projectionCountOfMeasure ν u E width (circleAntipode w) =
      projectionCountOfMeasure ν u E width w := by
  have heq : projectionCoincidenceSet u E width (circleAntipode w) =
      projectionCoincidenceSet u E width w := by
    ext z
    simp only [projectionCoincidenceSet, mem_ofPred_eq, coe_circleAntipode,
      inner_neg_right, abs_neg]
  unfold projectionCountOfMeasure
  rw [heq]

theorem projectionCoincidenceSet_mono_width (u : ℕ) (E : ℝ) {width width' : ℝ}
    (hwidth : width ≤ width') (w : UnitCircle) :
    projectionCoincidenceSet u E width w ⊆ projectionCoincidenceSet u E width' w := by
  intro z hz
  exact hz.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hwidth (by positivity)) (by positivity))

theorem projectionCountOfMeasure_mono_width (ν : Measure Plane) [IsFiniteMeasure ν]
    (u : ℕ) (E : ℝ) {width width' : ℝ} (hwidth : width ≤ width') (w : UnitCircle) :
    projectionCountOfMeasure ν u E width w ≤ projectionCountOfMeasure ν u E width' w :=
  measureReal_mono (projectionCoincidenceSet_mono_width u E hwidth w) (measure_ne_top _ _)

/-- Definition 6.3's actual count, with its source measure normalized on the anchor cell. -/
def projectionCount (ρ : Measure Plane) (p u : ℕ) (E width : ℝ) (P : Fin 2 → ℤ) :
    UnitCircle → ℝ := projectionCountOfMeasure (projectionAnchorMeasure ρ p P) u E width

def projectionAverage (ρ : Measure Plane) (p u : ℕ) (E : ℝ) (P : Fin 2 → ℤ) : ℝ :=
  directionalAverage (projectionCount ρ p u E 2 P)

def projectionPassingDirections (ρ : Measure Plane) (p u : ℕ) (E width : ℝ)
    (P : Fin 2 → ℤ) : Set UnitCircle :=
  {w | projectionCount ρ p u E width P w ≤
    (2 : ℝ) ^ (2 * E) * projectionAverage ρ p u E P}

/-- Lemma 6.4 for the literal normalized-anchor pair count, at width two. -/
theorem circleArcLength_projection_failure_le (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (p u : ℕ) (E : ℝ) (P : Fin 2 → ℤ) (hP : 0 < unitCellWeight ρ p P) :
    circleArcLength (projectionPassingDirections ρ p u E 2 P)ᶜ ≤
      ENNReal.ofReal (2 * Real.pi * (2 : ℝ) ^ (-2 * E)) := by
  have := isProbabilityMeasure_projectionAnchorMeasure ρ p P hP
  have h := circleArcLength_directionalTestFailure_le (q := (2 : ℝ) ^ (2 * E))
    (Real.rpow_pos_of_pos (by norm_num) _)
    (integrable_projectionCountOfMeasure (projectionAnchorMeasure ρ p P) u E 2)
    (projectionCountOfMeasure_nonneg (projectionAnchorMeasure ρ p P) u E 2)
  have heq : (projectionPassingDirections ρ p u E 2 P)ᶜ =
      directionalTestFailure ((2 : ℝ) ^ (2 * E)) (projectionCount ρ p u E 2 P) := by
    ext w
    simp only [projectionPassingDirections, directionalTestFailure, mem_compl_iff,
      mem_ofPred_eq, not_le, projectionAverage]
  rw [heq]
  change circleArcLength (directionalTestFailure ((2 : ℝ) ^ (2 * E))
    (projectionCountOfMeasure (projectionAnchorMeasure ρ p P) u E 2)) ≤ _
  convert h using 1
  rw [div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [neg_mul]

end FalconerThetaGauge
