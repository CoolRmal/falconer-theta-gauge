module

public import FalconerThetaGauge.GaugeSeparatedMeasures

/-!
# Gauge Frostman bounds under positive similarities

The unit-square preparation in Proposition 5.6 uses a translation and a positive
scalar multiplication. The logarithmic gauge bound is preserved, with a finite
constant independent of the radius. The proof uses subadditivity of `t ↦ t ^ θ`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology

namespace FalconerThetaGauge

namespace GaugeSeparatedMeasures

/-- A positive scalar multiplication followed by translation. -/
def affineMap (ℓ : ℝ) (z x : Plane) : Plane := z + ℓ • x

theorem continuous_affineMap (ℓ : ℝ) (z : Plane) : Continuous (affineMap ℓ z) := by
  unfold affineMap
  fun_prop

theorem affineMap_dist {ℓ : ℝ} (hℓ : 0 < ℓ) (z x y : Plane) :
    dist (affineMap ℓ z x) (affineMap ℓ z y) = ℓ * dist x y := by
  simp only [affineMap, dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hℓ]

theorem affineMap_right_inv {ℓ : ℝ} (hℓ : ℓ ≠ 0) (z x : Plane) :
    affineMap ℓ z (ℓ⁻¹ • (x - z)) = x := by
  simp [affineMap, smul_smul, mul_inv_cancel₀ hℓ]

theorem affineMap_injective {ℓ : ℝ} (hℓ : 0 < ℓ) (z : Plane) :
    Function.Injective (affineMap ℓ z) := by
  intro x y hxy
  have h := affineMap_dist hℓ z x y
  rw [hxy, dist_self] at h
  exact dist_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_left hℓ.ne')

theorem affineMap_preimage_ball {ℓ : ℝ} (hℓ : 0 < ℓ) (z x : Plane) (r : ℝ) :
    affineMap ℓ z ⁻¹' Metric.ball x r = Metric.ball (ℓ⁻¹ • (x - z)) (r / ℓ) := by
  ext y
  change dist (affineMap ℓ z y) x < r ↔ dist y (ℓ⁻¹ • (x - z)) < r / ℓ
  conv_lhs => rw [← affineMap_right_inv hℓ.ne' z x, affineMap_dist hℓ]
  rw [lt_div_iff₀ hℓ, mul_comm]

/-- The arbitrary-scale form of the gauge doubling estimate. -/
theorem realGauge_mul_le {θ a r : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (ha : 1 ≤ a) (hr : 0 < r) (har : a * r ≤ 1) :
    realGauge θ (a * r) ≤ (a * Real.exp (Real.log a ^ θ)) * realGauge θ r := by
  have hapos : 0 < a := zero_lt_one.trans_le ha
  have hlog : 0 ≤ Real.log (1 / (a * r)) :=
    Real.log_nonneg ((one_le_div₀ (mul_pos hapos hr)).mpr har)
  have hloga : 0 ≤ Real.log a := Real.log_nonneg ha
  have hlogeq : Real.log (1 / r) = Real.log (1 / (a * r)) + Real.log a := by
    simp only [one_div, Real.log_inv, Real.log_mul hapos.ne' hr.ne']
    ring
  have hpow : Real.log (1 / r) ^ θ ≤ Real.log (1 / (a * r)) ^ θ + Real.log a ^ θ := by
    rw [hlogeq]
    exact Real.rpow_add_le_add_rpow hlog hloga hθ₀ hθ₁
  have hexp : Real.exp (-(Real.log (1 / (a * r))) ^ θ) ≤
      Real.exp (Real.log a ^ θ) * Real.exp (-(Real.log (1 / r)) ^ θ) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    realGauge θ (a * r) ≤
        (a * r) * (Real.exp (Real.log a ^ θ) * Real.exp (-(Real.log (1 / r)) ^ θ)) :=
      mul_le_mul_of_nonneg_left hexp (mul_pos hapos hr).le
    _ = (a * Real.exp (Real.log a ^ θ)) * realGauge θ r := by
      unfold realGauge
      ring

theorem exists_realGauge_div_bound {θ ℓ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hℓ : 0 < ℓ) :
    ∃ D : ℝ, 0 < D ∧ ∀ r, 0 < r → r < 1 → r / ℓ < 1 →
      realGauge θ (r / ℓ) ≤ D * realGauge θ r := by
  by_cases hℓ1 : 1 ≤ ℓ
  · refine ⟨1, zero_lt_one, fun r hr hr1 _ ↦ ?_⟩
    rw [one_mul]
    exact realGauge_mono hθ₀ (div_pos hr hℓ).le
      ((div_le_self hr.le hℓ1)) hr1.le
  · have hinv : 1 ≤ ℓ⁻¹ := (one_le_inv₀ hℓ).mpr (not_le.mp hℓ1).le
    refine ⟨ℓ⁻¹ * Real.exp (Real.log ℓ⁻¹ ^ θ), by positivity, fun r hr _ hrℓ ↦ ?_⟩
    simpa only [div_eq_mul_inv, mul_comm r ℓ⁻¹] using
      realGauge_mul_le hθ₀ hθ₁ hinv hr
        (show ℓ⁻¹ * r ≤ 1 by simpa only [mul_comm, ← div_eq_mul_inv] using hrℓ.le)

/-- A positive affine similarity preserves the gauge Frostman property of a probability. -/
theorem exists_hasGaugeBallBound_map_affine {θ C ℓ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1)
    (hC : 0 < C) (hℓ : 0 < ℓ) (z : Plane) {μ : ProbabilityMeasure Plane}
    (hball : HasGaugeBallBound (μ : Measure Plane) θ C) :
    ∃ C' : ℝ, 0 < C' ∧ HasGaugeBallBound ((μ : Measure Plane).map (affineMap ℓ z)) θ C' := by
  obtain ⟨D, hD, hbound⟩ := exists_realGauge_div_bound hθ₀.le hθ₁ hℓ
  let δ : ℝ := min ℓ 1 / 2
  have hδ : 0 < δ := div_pos (lt_min hℓ zero_lt_one) (by norm_num)
  have hδ1 : δ < 1 := by
    have h := min_le_right ℓ 1
    dsimp [δ]
    linarith
  have hδℓ : δ ≤ ℓ := by
    have h := min_le_left ℓ 1
    have hp := (lt_min hℓ zero_lt_one).le
    dsimp [δ]
    linarith
  have hGaugeδ : 0 < realGauge θ δ := realGauge_pos θ hδ
  let C' : ℝ := C * D + (realGauge θ δ)⁻¹
  have hC' : 0 < C' := add_pos (mul_pos hC hD) (inv_pos.mpr hGaugeδ)
  refine ⟨C', hC', fun x r hr hr1 ↦ ?_⟩
  by_cases hrδ : r < δ
  · have hrℓ : r / ℓ < 1 := (div_lt_one hℓ).mpr (hrδ.trans_le hδℓ)
    calc
      (μ : Measure Plane).map (affineMap ℓ z) (Metric.ball x r) =
          (μ : Measure Plane) (Metric.ball (ℓ⁻¹ • (x - z)) (r / ℓ)) := by
        rw [Measure.map_apply (continuous_affineMap ℓ z).measurable
          Metric.isOpen_ball.measurableSet, affineMap_preimage_ball hℓ]
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (realGauge θ (r / ℓ)) :=
        hball _ _ (div_pos hr hℓ) hrℓ
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (D * realGauge θ r) :=
        mul_le_mul_right (ENNReal.ofReal_le_ofReal (hbound r hr hr1 hrℓ)) _
      _ = ENNReal.ofReal (C * D) * ENNReal.ofReal (realGauge θ r) := by
        rw [ENNReal.ofReal_mul hD.le, ← mul_assoc, ← ENNReal.ofReal_mul hC.le]
      _ ≤ ENNReal.ofReal C' * ENNReal.ofReal (realGauge θ r) :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal
          (le_add_of_nonneg_right (inv_pos.mpr hGaugeδ).le)) _
  · have hGauge : realGauge θ δ ≤ realGauge θ r :=
      realGauge_mono hθ₀.le hδ.le (not_lt.mp hrδ) hr1.le
    have hlarge : 1 ≤ C' * realGauge θ r := by
      calc
        1 = (realGauge θ δ)⁻¹ * realGauge θ δ := (inv_mul_cancel₀ hGaugeδ.ne').symm
        _ ≤ (realGauge θ δ)⁻¹ * realGauge θ r :=
          mul_le_mul_of_nonneg_left hGauge (inv_pos.mpr hGaugeδ).le
        _ ≤ C' * realGauge θ r :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (mul_pos hC hD).le)
            (realGauge_nonneg θ hr.le)
    have hmass : (μ : Measure Plane).map (affineMap ℓ z) (Metric.ball x r) ≤ 1 := by
      have := measure_mono (μ := (μ : Measure Plane).map (affineMap ℓ z))
        (subset_univ (Metric.ball x r))
      simpa [Measure.map_apply (continuous_affineMap ℓ z).measurable] using this
    refine hmass.trans ?_
    rw [← ENNReal.ofReal_mul hC'.le]
    simpa using ENNReal.ofReal_le_ofReal hlarge

end GaugeSeparatedMeasures

end FalconerThetaGauge
