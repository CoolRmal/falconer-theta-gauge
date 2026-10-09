module

public import FalconerThetaGauge.ScalarEnergyBinningFourierKernel

/-!
# Positive interval averages

The two-interval Fourier average is compared to the actual single frequency
window by translation and set inclusion. No Fourier inversion hypothesis is
needed for these elementary positive-integral comparisons.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Function

namespace FalconerThetaGauge

theorem integral_Icc_comp_add (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    (∫ u in Icc a b, f (t + u)) = ∫ r in Icc (a + t) (b + t), f r := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_comp_add_left,
    intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
  simp only [add_comm t]

theorem integral_Icc_split_of_integrableOn {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hf : IntegrableOn f (Icc a c)) :
    (∫ t in Icc a b, f t) + (∫ t in Icc b c, f t) = ∫ t in Icc a c, f t := by
  have hf₁ : IntervalIntegrable f volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
      (hf.mono_set (Icc_subset_Icc_right hbc))
  have hf₂ : IntervalIntegrable f volume b c :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hbc).2
      (hf.mono_set (Icc_subset_Icc_left hab))
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    ← intervalIntegral.integral_of_le hbc, ← intervalIntegral.integral_of_le (hab.trans hbc)]
  exact intervalIntegral.integral_add_adjacent_intervals hf₁ hf₂

theorem integrable_positive_box_average {f : ℝ → ℝ} (hf : Continuous f)
    (a b c d : ℝ) :
    Integrable (fun t ↦ ∫ u in Icc c d, f (t + u)) (volume.restrict (Icc a b)) := by
  have hc : Continuous (fun p : ℝ × ℝ ↦ f (p.1 + p.2)) :=
    hf.comp (continuous_fst.add continuous_snd)
  have hi : Integrable (fun p : ℝ × ℝ ↦ f (p.1 + p.2))
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
    rw [Measure.prod_restrict]
    exact hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  exact hi.integral_prod_left

/-- An upper comparison with the frequency window twice as wide. -/
theorem integral_positive_box_average_le {f : ℝ → ℝ} (hf : Continuous f)
    (hf₀ : ∀ r, 0 ≤ f r) {A : ℝ} (hA : 0 ≤ A) :
    (∫ t in Icc (-A) A, ∫ u in Icc (-A) A, f (t + u)) ≤
      2 * A * ∫ r in Icc (-(2 * A)) (2 * A), f r := by
  have hinner (t : ℝ) (ht : t ∈ Icc (-A) A) :
      (∫ u in Icc (-A) A, f (t + u)) ≤ ∫ r in Icc (-(2 * A)) (2 * A), f r := by
    rw [integral_Icc_comp_add f (by linarith)]
    apply setIntegral_mono_set (hf.integrableOn_Icc)
      (Eventually.of_forall fun r ↦ hf₀ r) (Eventually.of_forall ?_)
    intro r hr
    exact ⟨by linarith [hr.1, ht.1], by linarith [hr.2, ht.2]⟩
  calc
    _ ≤ ∫ _t in Icc (-A) A, ∫ r in Icc (-(2 * A)) (2 * A), f r :=
      setIntegral_mono_on (integrable_positive_box_average hf _ _ _ _) (integrable_const _)
        measurableSet_Icc hinner
    _ = _ := by
      rw [setIntegral_const, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      simp only [smul_eq_mul]
      ring

/-- The original frequency window is controlled by the two-interval average. -/
theorem mul_integral_le_positive_box_average {f : ℝ → ℝ} (hf : Continuous f)
    (hf₀ : ∀ r, 0 ≤ f r) {A : ℝ} (hA : 0 ≤ A) :
    A * (∫ r in Icc (-A) A, f r) ≤
      ∫ t in Icc (-A) A, ∫ u in Icc (-A) A, f (t + u) := by
  have hneg (t : ℝ) (ht : t ∈ Icc (-A) 0) :
      (∫ r in Icc (-A) 0, f r) ≤ ∫ u in Icc (-A) A, f (t + u) := by
    rw [integral_Icc_comp_add f (by linarith)]
    apply setIntegral_mono_set (hf.integrableOn_Icc)
      (Eventually.of_forall fun r ↦ hf₀ r) (Eventually.of_forall ?_)
    intro r hr
    exact ⟨by linarith [hr.1, ht.2], by linarith [hr.2, ht.1]⟩
  have hpos (t : ℝ) (ht : t ∈ Icc 0 A) :
      (∫ r in Icc 0 A, f r) ≤ ∫ u in Icc (-A) A, f (t + u) := by
    rw [integral_Icc_comp_add f (by linarith)]
    apply setIntegral_mono_set (hf.integrableOn_Icc)
      (Eventually.of_forall fun r ↦ hf₀ r) (Eventually.of_forall ?_)
    intro r hr
    exact ⟨by linarith [hr.1, ht.2], by linarith [hr.2, ht.1]⟩
  have hn := setIntegral_mono_on (integrable_const (∫ r in Icc (-A) 0, f r))
    (integrable_positive_box_average hf (-A) 0 (-A) A) measurableSet_Icc hneg
  have hp := setIntegral_mono_on (integrable_const (∫ r in Icc 0 A, f r))
    (integrable_positive_box_average hf 0 A (-A) A) measurableSet_Icc hpos
  simp only [setIntegral_const, Measure.real, Real.volume_Icc, sub_zero, zero_sub,
    neg_neg, ENNReal.toReal_ofReal hA, smul_eq_mul] at hn hp
  have hsplit := integral_Icc_split_of_integrableOn (neg_nonpos.2 hA) hA
    (integrable_positive_box_average hf (-A) A (-A) A)
  have hfsplit := integral_Icc_split_of_integrableOn (neg_nonpos.2 hA) hA hf.integrableOn_Icc
  rw [← hsplit, ← hfsplit, mul_add]
  exact add_le_add hn hp

end FalconerThetaGauge
