/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularFilteredMeasureMixturePieces
public import FalconerThetaGauge.FourierBilinearFiniteExpansion
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Genuine Fourier Cauchy--Schwarz for finite positive measure mixtures -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical ENNReal

namespace FalconerThetaGauge

theorem integrable_scalar_character (η : Measure ℝ) [IsFiniteMeasure η] (r : ℝ) :
    Integrable (fun s : ℝ ↦ Complex.exp ((r : ℂ) * (s : ℂ) * Complex.I)) η := by
  apply (integrable_const (1 : ℝ)).mono
  · exact (by fun_prop : Measurable (fun s : ℝ ↦
      Complex.exp ((r : ℂ) * (s : ℂ) * Complex.I))).aestronglyMeasurable
  · filter_upwards [] with s
    simp [Complex.norm_exp]

theorem angularScalarFourier_finite_mixture {ι : Type*} [Fintype ι]
    (η : ι → Measure ℝ) [∀ i, IsFiniteMeasure (η i)]
    (a : ι → ℝ≥0∞) (ha : ∀ i, a i ≠ ∞) (r : ℝ) :
    angularScalarFourier (Measure.sum (fun i ↦ a i • η i)) r =
      ∑ i, (a i).toReal * angularScalarFourier (η i) r := by
  simp only [angularScalarFourier, charFun_apply_real, Measure.sum_fintype]
  rw [integral_finsetSum_measure (fun i _ ↦
    (integrable_scalar_character (η i) (-r)).smul_measure (ha i))]
  simp only [integral_smul_measure, Complex.real_smul]

theorem integrableOn_scalarFourierAnnulus (η : Measure ℝ) [IsFiniteMeasure η] (s t : ℝ) :
    IntegrableOn (fun r ↦ ‖angularScalarFourier η r‖ ^ 2) (scalarFourierAnnulus s t) := by
  apply ((continuous_angularScalarFourier η).norm.pow 2).integrableOn_Icc.mono_set
    (show scalarFourierAnnulus s t ⊆ Icc (-((2 : ℝ) ^ t)) ((2 : ℝ) ^ t) from ?_)
  intro r hr
  exact abs_le.mp hr.2

/-- The exact weights remain in the estimate, with no count factor for the number of pieces. -/
theorem scalarFourierAnnulusIntegral_finite_mixture_le {ι : Type*} [Fintype ι]
    (η : ι → Measure ℝ) [∀ i, IsFiniteMeasure (η i)]
    (a : ι → ℝ≥0∞) (ha : ∀ i, a i ≠ ∞) (s t : ℝ) :
    scalarFourierAnnulusIntegral (Measure.sum (fun i ↦ a i • η i)) s t ≤
      (∑ i, (a i).toReal) * ∑ i, (a i).toReal * scalarFourierAnnulusIntegral (η i) s t := by
  have h := integral_norm_sum_sq_le_weighted Finset.univ
    (measurableSet_scalarFourierAnnulus s t)
    (fun i _ ↦ measurable_const : ∀ i ∈ Finset.univ,
      Measurable (fun _ : ℝ ↦ ((a i).toReal : ℂ)))
    (fun i _ ↦ (continuous_angularScalarFourier (η i)).measurable)
    (fun i _ ↦ integrableOn_scalarFourierAnnulus (η i) s t)
    (fun i _ ↦ ENNReal.toReal_nonneg)
    (fun i _ r _ ↦ by simp :
      ∀ i ∈ Finset.univ, ∀ r ∈ scalarFourierAnnulus s t,
        ‖((a i).toReal : ℂ)‖ ≤ (a i).toReal)
  simpa only [scalarFourierAnnulusIntegral,
    angularScalarFourier_finite_mixture η a ha, Complex.ofReal_mul] using h

theorem scalarFourierAnnulusIntegral_subprobability_mixture_le
    {ι : Type*} [Fintype ι] (η : ι → Measure ℝ) [∀ i, IsFiniteMeasure (η i)]
    (a : ι → ℝ≥0∞) (ha : ∀ i, a i ≠ ∞) (hmass : ∑ i, (a i).toReal ≤ 1)
    (s t : ℝ) :
    scalarFourierAnnulusIntegral (Measure.sum (fun i ↦ a i • η i)) s t ≤
      ∑ i, (a i).toReal * scalarFourierAnnulusIntegral (η i) s t := by
  apply (scalarFourierAnnulusIntegral_finite_mixture_le η a ha s t).trans
  exact (mul_le_mul_of_nonneg_right hmass
    (Finset.sum_nonneg fun i _ ↦ mul_nonneg ENNReal.toReal_nonneg
      (scalarFourierAnnulusIntegral_nonneg (η i) s t))).trans_eq (one_mul _)

end FalconerThetaGauge
