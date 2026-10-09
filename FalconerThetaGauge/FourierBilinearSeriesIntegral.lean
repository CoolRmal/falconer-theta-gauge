/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierBilinearCoefficientSeries
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # Genuine integration of the coefficient Cauchy--Schwarz series -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Finset

namespace FalconerThetaGauge

theorem integral_norm_tsum_mul_sq_le_weighted {ι α : Type*} [Countable ι]
    [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {c z : ι → α → ℂ} {a : ι → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hc : ∀ i, Measurable (c i)) (hz : ∀ i, Measurable (z i))
    (ha : ∀ i, 0 ≤ a i) (has : Summable a)
    (hca : ∀ i, ∀ᵐ x ∂μ, ‖c i x‖ ≤ a i)
    (hzB : ∀ i, ∀ᵐ x ∂μ, ‖z i x‖ ^ 2 ≤ B) :
    (∫ x, ‖∑' i, c i x * z i x‖ ^ 2 ∂μ) ≤
      (∑' i, a i) * ∑' i, a i * (∫ x, ‖z i x‖ ^ 2 ∂μ) := by
  have hsum : ∀ᵐ x ∂μ, Summable (fun i ↦ a i * ‖z i x‖ ^ 2) := by
    filter_upwards [ae_all_iff.mpr hzB] with x hx
    apply (has.mul_right B).of_nonneg_of_le (fun i ↦ mul_nonneg (ha i) (sq_nonneg _))
    exact fun i ↦ mul_le_mul_of_nonneg_left (hx i) (ha i)
  have hmajorBound : ∀ᵐ x ∂μ, ‖∑' i, a i * ‖z i x‖ ^ 2‖ ≤ (∑' i, a i) * B := by
    filter_upwards [ae_all_iff.mpr hzB, hsum] with x hx hs
    rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun i ↦
      mul_nonneg (ha i) (sq_nonneg _))), ← tsum_mul_right]
    exact Summable.tsum_le_tsum (fun i ↦ mul_le_mul_of_nonneg_left (hx i) (ha i))
      hs (has.mul_right B)
  have hmajor : Integrable (fun x ↦ ∑' i, a i * ‖z i x‖ ^ 2) μ :=
    (integrable_const ((∑' i, a i) * B)).mono
      (Measurable.tsum (fun i ↦ ((hz i).norm.pow_const 2).const_mul (a i))).aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (tsum_nonneg ha) hB)] using hmajorBound)
  have hpoint : ∀ᵐ x ∂μ, ‖∑' i, c i x * z i x‖ ^ 2 ≤
      (∑' i, a i) * ∑' i, a i * ‖z i x‖ ^ 2 := by
    filter_upwards [ae_all_iff.mpr hca, hsum] with x hx hs
    exact norm_tsum_mul_sq_le_weighted ha hx has hs
  have hint : Integrable (fun x ↦ ‖∑' i, c i x * z i x‖ ^ 2) μ := by
    apply (hmajor.const_mul (∑' i, a i)).mono
    · exact ((Measurable.tsum (fun i ↦ (hc i).mul (hz i))).norm.pow_const
        2).aestronglyMeasurable
    · filter_upwards [hpoint] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (tsum_nonneg ha)
          (tsum_nonneg (fun i ↦ mul_nonneg (ha i) (sq_nonneg _))))]
      exact hx
  have hEq : (∫ x, ∑' i, a i * ‖z i x‖ ^ 2 ∂μ) =
      ∑' i, a i * (∫ x, ‖z i x‖ ^ 2 ∂μ) := by
    have hdom := hasSum_integral_of_dominated_convergence
      (fun i (_x : α) ↦ a i * B)
      (fun i ↦ ((hz i).norm.pow_const 2).const_mul (a i) |>.aestronglyMeasurable)
      (fun i ↦ (hzB i).mono (fun x hx ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ha i) (sq_nonneg _))]
        exact mul_le_mul_of_nonneg_left hx (ha i)))
      (Eventually.of_forall (fun _ ↦ has.mul_right B))
      (integrable_const ((∑' i, a i * B)))
      (hsum.mono (fun _ hs ↦ hs.hasSum))
    simpa only [integral_const_mul] using hdom.tsum_eq.symm
  calc
    _ ≤ ∫ x, (∑' i, a i) * ∑' i, a i * ‖z i x‖ ^ 2 ∂μ :=
      integral_mono_ae hint (hmajor.const_mul _) hpoint
    _ = _ := by rw [integral_const_mul, hEq]

end FalconerThetaGauge
