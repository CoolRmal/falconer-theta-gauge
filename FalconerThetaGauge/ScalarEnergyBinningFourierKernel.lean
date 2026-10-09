module

public import FalconerThetaGauge.ScalarEnergyBinningKernel
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# Scalar interval Fourier kernels

These lemmas implement the sinc-squared kernels used in Lemma 7.3(iv).
All Fourier transforms in this file use the manuscript's angular frequency
convention `exp (-I * r * s)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal RealInnerProductSpace

namespace FalconerThetaGauge

/-- The scalar Fourier transform in the manuscript's angular-frequency convention. -/
def angularScalarFourier (η : Measure ℝ) (r : ℝ) : ℂ := charFun η (-r)

theorem norm_angularScalarFourier (η : Measure ℝ) (r : ℝ) :
    ‖angularScalarFourier η r‖ = ‖charFun η r‖ := by
  simp [angularScalarFourier, charFun_neg]

@[fun_prop]
theorem continuous_angularScalarFourier (η : Measure ℝ) [IsFiniteMeasure η] :
    Continuous (angularScalarFourier η) := continuous_charFun.comp continuous_neg

/-- The source's Fejér kernel is uniformly positive on the collision window. -/
theorem half_le_sinc_sq_of_abs_le_half {u : ℝ} (hu : |u| ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ Real.sinc u ^ (2 : ℕ) := by
  have ha : 0 ≤ |u| := abs_nonneg _
  have hs : Real.sinc |u| = Real.sinc u := by
    rcases le_total 0 u with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, Real.sinc_neg]
  by_cases hzero : |u| = 0
  · have hu0 : u = 0 := abs_eq_zero.1 hzero
    simp [hu0]
    norm_num
  have hpos : 0 < |u| := lt_of_le_of_ne ha (Ne.symm hzero)
  have hl : 23 / 24 ≤ Real.sinc |u| := by
    rw [Real.sinc_of_ne_zero hzero]
    apply (le_div_iff₀ hpos).2
    have hb := Real.sin_ge_sub_cube ha
    have hsq : |u| ^ (2 : ℕ) ≤ 1 / 4 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq ha]
  rw [hs] at hl
  nlinarith

/-- The sinc kernel has the precise polynomial envelope used in the source. -/
theorem four_mul_sinc_sq_le_decay (u : ℝ) :
    4 * Real.sinc u ^ (2 : ℕ) ≤ 16 * (1 + |u|) ^ (-2 : ℝ) := by
  have hbase : 0 < 1 + |u| := by positivity
  rw [Real.rpow_neg hbase.le, Real.rpow_two]
  apply (le_mul_inv_iff₀ (sq_pos_of_pos hbase)).2
  by_cases hu : |u| ≤ 1
  · have hs := Real.abs_sinc_le_one u
    have hsq : Real.sinc u ^ (2 : ℕ) ≤ 1 := by
      have hl := (abs_le.1 hs).1
      have hu := (abs_le.1 hs).2
      nlinarith
    have hB : (1 + |u|) ^ (2 : ℕ) ≤ 4 := by nlinarith [abs_nonneg u]
    nlinarith [mul_le_mul hsq hB (sq_nonneg (1 + |u|)) (by norm_num : (0 : ℝ) ≤ 1)]
  · have hup : 0 < |u| := by linarith [abs_nonneg u]
    have hun : u ≠ 0 := by exact fun h ↦ by simp [h] at hup
    rw [Real.sinc_of_ne_zero hun]
    have hs : (Real.sin u) ^ (2 : ℕ) ≤ 1 := Real.sin_sq_le_one u
    have hB : (1 + |u|) ^ (2 : ℕ) ≤ 4 * u ^ (2 : ℕ) := by
      nlinarith [sq_abs u, abs_nonneg u]
    have hu2 : 0 < u ^ (2 : ℕ) := sq_pos_of_ne_zero hun
    rw [div_pow]
    rw [show 4 * (Real.sin u ^ 2 / u ^ 2) * (1 + |u|) ^ 2 =
      (4 * Real.sin u ^ 2 * (1 + |u|) ^ 2) / u ^ 2 by ring]
    apply (div_le_iff₀ hu2).2
    nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg (1 + |u|))]

/-- Fourier integral of the centered interval, including frequency zero. -/
theorem integral_interval_character_eq_sinc {A : ℝ} (hA : 0 ≤ A) (d : ℝ) :
    (∫ t in Icc (-A) A, Complex.exp ((d * t : ℝ) * Complex.I)) =
      (2 * A * Real.sinc (A * d) : ℝ) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  have h := intervalIntegral.smul_integral_comp_mul_left
    (f := fun t : ℝ ↦ Complex.exp ((t : ℂ) * Complex.I)) d
    (a := -A) (b := A)
  simp only [Complex.real_smul] at h
  rw [show d * (-A) = -(A * d) by ring, show d * A = A * d by ring,
    integral_exp_mul_I_eq_sinc] at h
  by_cases hd : d = 0
  · simp [hd]
    ring
  have hphase : (fun t : ℝ ↦ Complex.exp ((↑(d * t) : ℂ) * Complex.I)) =
      fun t : ℝ ↦ Complex.exp ((d : ℂ) * t * Complex.I) := by
    ext t
    push_cast
    rfl
  rw [hphase]
  apply (mul_left_cancel₀ (show (d : ℂ) ≠ 0 by exact_mod_cast hd))
  convert h using 1 <;> push_cast <;> ring

/-- Squared Fourier modulus is the Fourier transform of the actual difference measure. -/
theorem charFun_scalar_difference_eq_norm_sq (η : Measure ℝ) [IsFiniteMeasure η] (r : ℝ) :
    charFun ((η.prod η).map (fun p ↦ p.1 - p.2)) r = (‖charFun η r‖ ^ (2 : ℕ) : ℝ) := by
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  have hphase (p : ℝ × ℝ) :
      Complex.exp (⟪p.1 - p.2, r⟫ * Complex.I) =
        Complex.exp (⟪p.1, r⟫ * Complex.I) * Complex.exp (⟪p.2, -r⟫ * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [inner_sub_left, inner_neg_right, Complex.ofReal_sub, Complex.ofReal_neg]
    ring
  simp_rw [hphase]
  rw [integral_prod_mul (fun s : ℝ ↦ Complex.exp (⟪s, r⟫ * Complex.I))
    (fun s : ℝ ↦ Complex.exp (⟪s, -r⟫ * Complex.I))]
  change charFun η r * charFun η (-r) = _
  rw [charFun_neg, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The actual two-interval Fourier average is a nonnegative sinc-square kernel. -/
theorem integral_box_charFun_eq_sinc_sq (δ : Measure ℝ) [IsFiniteMeasure δ]
    {A : ℝ} (hA : 0 ≤ A) :
    (∫ q : ℝ × ℝ, charFun δ (q.1 + q.2)
      ∂(volume.restrict (Icc (-A) A)).prod (volume.restrict (Icc (-A) A))) =
      ∫ d, ((2 * A * Real.sinc (A * d)) ^ (2 : ℕ) : ℝ) ∂δ := by
  let ν : Measure ℝ := volume.restrict (Icc (-A) A)
  have : IsFiniteMeasure ν := by dsimp [ν]; infer_instance
  have hf : Integrable (fun p : (ℝ × ℝ) × ℝ ↦
      Complex.exp (((p.1.1 + p.1.2) * p.2 : ℝ) * Complex.I)) ((ν.prod ν).prod δ) := by
    apply (integrable_const (1 : ℝ)).mono (by fun_prop)
    exact Eventually.of_forall fun p ↦ by
      rw [Complex.norm_exp]
      simp
  simp_rw [charFun_apply_real]
  simp only [Complex.ofReal_mul] at hf
  rw [integral_integral_swap hf]
  simp_rw [← Complex.ofReal_mul]
  have hphase (d : ℝ) (q : ℝ × ℝ) :
      Complex.exp (((q.1 + q.2) * d : ℝ) * Complex.I) =
        Complex.exp ((d * q.1 : ℝ) * Complex.I) *
          Complex.exp ((d * q.2 : ℝ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hphase]
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [] with d
  rw [integral_prod_mul (fun t : ℝ ↦ Complex.exp ((d * t : ℝ) * Complex.I))
    (fun t : ℝ ↦ Complex.exp ((d * t : ℝ) * Complex.I))]
  rw [integral_interval_character_eq_sinc hA]
  simp only [pow_two, Complex.ofReal_mul]

/-- The exact positive Fourier/spatial identity used for both estimates in Lemma 7.3(iv). -/
theorem integral_integral_fourier_box_eq_sinc_sq (η : Measure ℝ) [IsFiniteMeasure η]
    {A : ℝ} (hA : 0 ≤ A) :
    (∫ t in Icc (-A) A, ∫ u in Icc (-A) A,
      ‖angularScalarFourier η (t + u)‖ ^ (2 : ℕ)) =
      ∫ p : ℝ × ℝ, (2 * A * Real.sinc (A * (p.1 - p.2))) ^ (2 : ℕ) ∂η.prod η := by
  have h := integral_box_charFun_eq_sinc_sq ((η.prod η).map (fun p ↦ p.1 - p.2)) hA
  simp_rw [charFun_scalar_difference_eq_norm_sq, ← norm_angularScalarFourier] at h
  rw [integral_map (by fun_prop) (by fun_prop)] at h
  simp only [integral_complex_ofReal] at h
  have hc : Continuous (fun p : ℝ × ℝ ↦ ‖angularScalarFourier η (p.1 + p.2)‖ ^ (2 : ℕ)) :=
    ((continuous_angularScalarFourier η).comp (continuous_fst.add continuous_snd)).norm.pow 2
  have hf : Integrable (fun p : ℝ × ℝ ↦ ‖angularScalarFourier η (p.1 + p.2)‖ ^ (2 : ℕ))
      ((volume.restrict (Icc (-A) A)).prod (volume.restrict (Icc (-A) A))) := by
    rw [Measure.prod_restrict]
    exact hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hreal := Complex.ofReal_inj.mp h
  rw [integral_prod _ hf] at hreal
  exact hreal

end FalconerThetaGauge
