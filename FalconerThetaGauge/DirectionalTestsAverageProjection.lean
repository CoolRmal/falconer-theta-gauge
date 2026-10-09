module

public import FalconerThetaGauge.DirectionalTestsAverageBands
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Genuine Fubini reduction of actual projection averages to pair distances -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

/-- The literal angular collision majorant, retaining the correct value on the diagonal. -/
def angularCollisionMajorant (η : ℝ) (v : Plane) : ℝ :=
  if v = 0 then 1 else min 1 (η / ‖v‖)

theorem measurable_angularCollisionMajorant (η : ℝ) :
    Measurable (angularCollisionMajorant η) := by
  exact Measurable.ite (measurableSet_singleton (0 : Plane)) measurable_const
    (measurable_const.min (measurable_const.div continuous_norm.measurable))

theorem angularCollisionMajorant_mem_Icc {η : ℝ} (hη : 0 ≤ η) (v : Plane) :
    angularCollisionMajorant η v ∈ Icc 0 1 := by
  unfold angularCollisionMajorant
  split_ifs
  · exact ⟨by norm_num, le_rfl⟩
  · exact ⟨le_min (by norm_num) (div_nonneg hη (norm_nonneg _)), min_le_left _ _⟩

theorem circleArcLength_dotDirectionBand_le_majorant {η : ℝ} (hη : 0 ≤ η) (v : Plane) :
    circleArcLength (dotDirectionBand v η) ≤
      ENNReal.ofReal (2 * Real.pi * angularCollisionMajorant η v) := by
  by_cases hv : v = 0
  · simp only [angularCollisionMajorant, hv, ite_true, mul_one]
    calc
      _ ≤ circleArcLength univ := measure_mono (subset_univ _)
      _ = _ := circleArcLength_univ
  · simpa only [angularCollisionMajorant, ite_eq_right hv] using
      circleArcLength_dotDirectionBand_le v hv hη

theorem integrable_angularCollisionMajorant_pair (ν : Measure Plane) [IsProbabilityMeasure ν]
    {η : ℝ} (hη : 0 ≤ η) :
    Integrable (fun zz : Plane × Plane ↦ angularCollisionMajorant η (zz.1 - zz.2)) (ν.prod ν) := by
  have hm : Measurable (fun zz : Plane × Plane ↦ angularCollisionMajorant η (zz.1 - zz.2)) :=
    (measurable_angularCollisionMajorant η).comp (measurable_fst.sub measurable_snd)
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun zz ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (angularCollisionMajorant_mem_Icc hη _).1]
    exact (angularCollisionMajorant_mem_Icc hη _).2)

/-- Exact Fubini for the actual normalized-source projection count and actual circle arc length. -/
theorem integral_projectionCount_eq_integral_arcBand (ν : Measure Plane) [IsProbabilityMeasure ν]
    (u : ℕ) (E width : ℝ) :
    (∫ w, projectionCountOfMeasure ν u E width w ∂circleArcLength) =
      ∫ zz : Plane × Plane, circleArcLength.real
        (dotDirectionBand (zz.1 - zz.2) (width * (2 : ℝ) ^ (-(u : ℝ)) * (2 : ℝ) ^ (2 * E)))
        ∂ν.prod ν := by
  let S : Set (UnitCircle × (Plane × Plane)) :=
    {p | p.2 ∈ projectionCoincidenceSet u E width p.1}
  have hS : MeasurableSet S := measurableSet_projectionCoincidenceRelation u E width
  let F : UnitCircle → (Plane × Plane) → ℝ := fun w zz ↦ S.indicator (fun _ ↦ 1) (w, zz)
  have hF : Integrable (Function.uncurry F) (circleArcLength.prod (ν.prod ν)) := by
    apply Integrable.of_bound (measurable_const.indicator hS).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun p ↦ by simp only [indicator]; split_ifs <;> norm_num)
  have hleft (w : UnitCircle) : (∫ zz, F w zz ∂ν.prod ν) =
      projectionCountOfMeasure ν u E width w := by
    have heq : F w = (projectionCoincidenceSet u E width w).indicator (fun _ ↦ (1 : ℝ)) := by
      ext zz
      simp only [F, S, indicator, mem_ofPred_eq]
    have hs : MeasurableSet (projectionCoincidenceSet u E width w) := by
      change MeasurableSet {zz : Plane × Plane | |inner ℝ (zz.1 - zz.2) (w : Plane)| ≤
        width * (2 : ℝ) ^ (-(u : ℝ)) * (2 : ℝ) ^ (2 * E)}
      apply (isClosed_le _ continuous_const).measurableSet
      fun_prop
    rw [heq, integral_indicator_const _ hs]
    simp only [projectionCountOfMeasure, smul_eq_mul, mul_one]
  have hright (zz : Plane × Plane) : (∫ w, F w zz ∂circleArcLength) =
      circleArcLength.real (dotDirectionBand (zz.1 - zz.2)
        (width * (2 : ℝ) ^ (-(u : ℝ)) * (2 : ℝ) ^ (2 * E))) := by
    have heq : (fun w ↦ F w zz) = (dotDirectionBand (zz.1 - zz.2)
        (width * (2 : ℝ) ^ (-(u : ℝ)) * (2 : ℝ) ^ (2 * E))).indicator (fun _ ↦ (1 : ℝ)) := by
      ext w
      simp only [F, S, projectionCoincidenceSet, dotDirectionBand, indicator, mem_ofPred_eq]
      rfl
    rw [heq, integral_indicator_const _ (measurableSet_dotDirectionBand _ _)]
    simp only [smul_eq_mul, mul_one]
  calc
    _ = ∫ w, ∫ zz, F w zz ∂ν.prod ν ∂circleArcLength :=
      integral_congr_ae (Filter.Eventually.of_forall (fun w ↦ (hleft w).symm))
    _ = ∫ zz, ∫ w, F w zz ∂circleArcLength ∂ν.prod ν := integral_integral_swap hF
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hright)

/-- The source projection average is bounded by the actual capped inverse-distance pair integral. -/
theorem directionalAverage_projectionCount_le_collision (ν : Measure Plane)
    [IsProbabilityMeasure ν] (u : ℕ) (E : ℝ) {width : ℝ} (hwidth : 0 ≤ width) :
    directionalAverage (projectionCountOfMeasure ν u E width) ≤
      ∫ zz : Plane × Plane, angularCollisionMajorant
        (width * (2 : ℝ) ^ (-(u : ℝ)) * (2 : ℝ) ^ (2 * E)) (zz.1 - zz.2) ∂ν.prod ν := by
  let η := width * (2 : ℝ) ^ (-(u : ℝ)) * (2 : ℝ) ^ (2 * E)
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hcount := integrable_projectionCountOfMeasure ν u E width
  have hinner : Integrable (fun zz : Plane × Plane ↦ circleArcLength.real
      (dotDirectionBand (zz.1 - zz.2) η)) (ν.prod ν) := by
    have hmeas : Measurable (fun zz : Plane × Plane ↦ circleArcLength.real
        (dotDirectionBand (zz.1 - zz.2) η)) := by
      have h := (measurable_measure_prodMk_right (μ := circleArcLength)
        (measurableSet_projectionCoincidenceRelation u E width)).ennreal_toReal
      exact h
    apply Integrable.of_bound hmeas.aestronglyMeasurable (2 * Real.pi)
    exact Filter.Eventually.of_forall (fun zz ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact (measureReal_mono (subset_univ _) (measure_ne_top _ _)).trans_eq
        (by simp only [Measure.real, circleArcLength_univ, ENNReal.toReal_ofReal
          (by positivity : 0 ≤ 2 * Real.pi)]))
  have hint := integral_mono hinner
    ((integrable_angularCollisionMajorant_pair ν hη).const_mul (2 * Real.pi))
    (fun zz ↦ ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg (by positivity) (angularCollisionMajorant_mem_Icc hη _).1)
      (circleArcLength_dotDirectionBand_le_majorant hη _))
  rw [integral_const_mul] at hint
  unfold directionalAverage
  rw [integral_projectionCount_eq_integral_arcBand]
  have h := mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr (by positivity : 0 ≤ 2 * Real.pi))
  convert h using 1
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_mul]

end FalconerThetaGauge
