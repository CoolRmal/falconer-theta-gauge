module

public import FalconerThetaGauge.FiniteGraphSchur
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Integrated Schur bounds retaining oscillatory cancellation in unlinked pairs -/

@[expose] public section

noncomputable section

open MeasureTheory Finset
open scoped InnerProductSpace

namespace FalconerThetaGauge

theorem integrable_real_inner_of_memLp_two {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {μ : Measure α} {f g : α → F}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x ↦ inner ℝ (f x) (g x)) μ := by
  apply (hf.norm.integrable_mul hg.norm).mono
  · exact hf.aestronglyMeasurable.inner hg.aestronglyMeasurable
  · filter_upwards [] with x
    simpa only [Pi.mul_apply, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))] using abs_real_inner_le_norm (f x) (g x)

/-- Each unlinked error retains its actual oscillatory cancellation after integration. -/
theorem integral_norm_sum_sq_le_graph_schur {ι α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (μ : Measure α)
    (s : Finset ι) (linked : ι → ι → Prop) [DecidableRel linked]
    (hsym : ∀ ⦃i j⦄, linked i j → linked j i) (z : ι → α → F) {D : ℝ}
    (hdegree : ∀ i ∈ s, ((s.filter (linked i)).card : ℝ) ≤ D)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, Integrable (fun x ↦ inner ℝ (z i x) (z j x)) μ) :
    (∫ x, ‖∑ i ∈ s, z i x‖ ^ 2 ∂μ) ≤
      D * (∑ i ∈ s, ∫ x, ‖z i x‖ ^ 2 ∂μ) +
      ∑ i ∈ s, ∑ j ∈ s,
        if linked i j then 0 else |∫ x, inner ℝ (z i x) (z j x) ∂μ| := by
  have hdiag : ∀ i ∈ s, Integrable (fun x ↦ ‖z i x‖ ^ 2) μ := by
    intro i hi
    simpa only [real_inner_self_eq_norm_sq] using hcross i hi i hi
  have hlinked : ∀ i ∈ s, ∀ j ∈ s,
      Integrable (fun x ↦ if linked i j then inner ℝ (z i x) (z j x) else 0) μ := by
    intro i hi j hj
    by_cases h : linked i j
    · simpa only [ite_eq_left h] using hcross i hi j hj
    · simp only [ite_eq_right h]
      exact integrable_const_iff.mpr (Or.inl rfl)
  have hidentity : (∫ x, ‖∑ i ∈ s, z i x‖ ^ 2 ∂μ) =
      ∑ i ∈ s, ∑ j ∈ s, ∫ x, inner ℝ (z i x) (z j x) ∂μ := by
    have he : ∀ x, ‖∑ i ∈ s, z i x‖ ^ 2 =
        ∑ i ∈ s, ∑ j ∈ s, inner ℝ (z i x) (z j x) := by
      intro x
      rw [← real_inner_self_eq_norm_sq, sum_inner]
      simp_rw [inner_sum]
    simp_rw [he]
    rw [integral_finsetSum s (fun i hi ↦ integrable_finsetSum s (hcross i hi))]
    apply sum_congr rfl
    intro i hi
    exact integral_finsetSum s (hcross i hi)
  have hlink : (∑ i ∈ s, ∑ j ∈ s,
      if linked i j then (∫ x, inner ℝ (z i x) (z j x) ∂μ) else 0) ≤
      D * (∑ i ∈ s, ∫ x, ‖z i x‖ ^ 2 ∂μ) := by
    have he : (∑ i ∈ s, ∑ j ∈ s,
        if linked i j then (∫ x, inner ℝ (z i x) (z j x) ∂μ) else 0) =
        ∫ x, ∑ i ∈ s, ∑ j ∈ s,
          if linked i j then inner ℝ (z i x) (z j x) else 0 ∂μ := by
      rw [integral_finsetSum s (fun i hi ↦ integrable_finsetSum s (hlinked i hi))]
      apply sum_congr rfl
      intro i hi
      rw [integral_finsetSum s (hlinked i hi)]
      apply sum_congr rfl
      intro j hj
      by_cases h : linked i j <;> simp only [h, ite_true, ite_false, integral_zero]
    rw [he]
    calc
      _ ≤ ∫ x, D * ∑ i ∈ s, ‖z i x‖ ^ 2 ∂μ := by
        apply integral_mono (integrable_finsetSum s
          (fun i hi ↦ integrable_finsetSum s (hlinked i hi)))
          ((integrable_finsetSum s hdiag).const_mul D)
        intro x
        calc
          _ ≤ ∑ i ∈ s, ∑ j ∈ s, if linked i j then ‖z i x‖ * ‖z j x‖ else 0 := by
            apply sum_le_sum
            intro i hi
            apply sum_le_sum
            intro j hj
            by_cases h : linked i j
            · simpa only [ite_eq_left h] using real_inner_le_norm (z i x) (z j x)
            · simp only [ite_eq_right h, le_refl]
          _ ≤ _ := finite_graph_schur s linked hsym (fun i ↦ ‖z i x‖) hdegree
      _ = _ := by rw [integral_const_mul, integral_finsetSum s hdiag]
  rw [hidentity]
  calc
    _ = (∑ i ∈ s, ∑ j ∈ s,
          if linked i j then (∫ x, inner ℝ (z i x) (z j x) ∂μ) else 0) +
        ∑ i ∈ s, ∑ j ∈ s,
          if linked i j then 0 else (∫ x, inner ℝ (z i x) (z j x) ∂μ) := by
      simp_rw [← sum_add_distrib]
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      split_ifs <;> simp only [add_zero, zero_add]
    _ ≤ _ := add_le_add hlink (by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      by_cases h : linked i j
      · simp only [ite_eq_left h, le_refl]
      · simpa only [ite_eq_right h] using
          le_abs_self (∫ x, inner ℝ (z i x) (z j x) ∂μ))

end FalconerThetaGauge
