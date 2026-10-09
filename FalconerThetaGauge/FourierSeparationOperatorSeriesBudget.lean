/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierSeparationOperatorSeries

/-! # Actual class membership and coefficient budgets of the countable operator series -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric Polynomial Finset
open scoped Classical ContDiff

namespace FalconerThetaGauge

theorem scheduledPairSeparatedLeftSymbol_mem_class (p : Polynomial ℂ)
    (d : ScheduledSymbolData) {x₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ)
    {X : Set Plane} (hX : MeasurableSet X) (hXball : X ⊆ closedBall x₀ ρ)
    (ρ₁ : Measure Plane) (E width : ℝ) (K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest)
    (z : ScheduledPairOperatorBranch p I₁ I₂ × ℕ) :
    scheduledPairSeparatedLeftSymbol p d ρ₁ X E width K I₁ I₂ x₀ ρ z ∈
      scheduledSymbolClass ρ₁ E width K I₁ (d.order I₁ + p.natDegree) := by
  exact separation_left_symbol_mem_class hρ hX hXball ρ₁ E width K I₁ _
    ⟨scheduledPairOperatorLeftData p d I₁ I₂ z.1,
      scheduledPairOperatorLeftData_order_le p d I₁ I₂ z.1, rfl⟩ z.2

theorem scheduledPairSeparatedRightSymbol_mem_class (p : Polynomial ℂ)
    (d : ScheduledSymbolData) {y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ)
    {Y : Set Plane} (hY : MeasurableSet Y) (hYball : Y ⊆ closedBall y₀ ρ)
    (ρ₂ : Measure Plane) (E width : ℝ) (K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest)
    (z : ScheduledPairOperatorBranch p I₁ I₂ × ℕ) :
    scheduledPairSeparatedRightSymbol p d ρ₂ Y E width K I₁ I₂ y₀ ρ z ∈
      scheduledSymbolClass ρ₂ E width K I₂ (d.order I₂ + p.natDegree) := by
  exact separation_right_symbol_mem_class hρ hY hYball ρ₂ E width K I₂ _
    ⟨scheduledPairOperatorRightData p d I₁ I₂ z.1,
      scheduledPairOperatorRightData_order_le p d I₁ I₂ z.1, rfl⟩ z.2

theorem summable_finite_norm_mul_abs {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (a : ℕ → ℝ) (ha : Summable (fun n ↦ |a n|)) :
    Summable (fun z : ι × ℕ ↦ ‖c z.1‖ * |a z.2|) := by
  apply (summable_prod_of_nonneg (fun z : ι × ℕ ↦
    mul_nonneg (norm_nonneg (c z.1)) (abs_nonneg (a z.2)))).mpr
  constructor
  · intro b
    exact ha.mul_left ‖c b‖
  · exact Summable.of_finite (L := SummationFilter.unconditional ι)

theorem summable_norm_scheduledPairSeparatedCoefficient (p : Polynomial ℂ) (j : ℕ)
    (d₁ d₂ : ScheduledSymbolData) (E : ℝ) (I₁ I₂ : Finset ProfileScheduleTest)
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀) :
    Summable (fun z : ScheduledPairOperatorBranch p I₁ I₂ × ℕ ↦
      ‖scheduledPairSeparatedCoefficient p j d₁ d₂ E I₁ I₂ x₀ y₀ ρ z‖) := by
  have hs := summable_spatialInversePowerSequenceCoefficient_abs j hρ hsep
  simpa only [scheduledPairSeparatedCoefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    using summable_finite_norm_mul_abs
      (scheduledPairOperatorBranchCoefficient p d₁ d₂ E I₁ I₂)
      (spatialInversePowerSequenceCoefficient j x₀ y₀ ρ) hs

theorem tsum_norm_scheduledPairSeparatedCoefficient_eq (p : Polynomial ℂ) (j : ℕ)
    (d₁ d₂ : ScheduledSymbolData) (E : ℝ) (I₁ I₂ : Finset ProfileScheduleTest)
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀) :
    (∑' z : ScheduledPairOperatorBranch p I₁ I₂ × ℕ,
      ‖scheduledPairSeparatedCoefficient p j d₁ d₂ E I₁ I₂ x₀ y₀ ρ z‖) =
      (∑ b : ScheduledPairOperatorBranch p I₁ I₂,
        ‖scheduledPairOperatorBranchCoefficient p d₁ d₂ E I₁ I₂ b‖) *
        ∑' n, |spatialInversePowerSequenceCoefficient j x₀ y₀ ρ n| := by
  have hs := summable_spatialInversePowerSequenceCoefficient_abs j hρ hsep
  have ht := summable_norm_scheduledPairSeparatedCoefficient p j d₁ d₂ E I₁ I₂ hρ hsep
  rw [ht.tsum_prod' (fun b ↦ by
    simpa only [scheduledPairSeparatedCoefficient, norm_mul, Complex.norm_real,
      Real.norm_eq_abs] using hs.mul_left
        ‖scheduledPairOperatorBranchCoefficient p d₁ d₂ E I₁ I₂ b‖)]
  simp only [scheduledPairSeparatedCoefficient, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, tsum_mul_left, tsum_fintype]
  exact (sum_mul _ _ _).symm

theorem tsum_norm_scheduledPairSeparatedCoefficient_le (p : Polynomial ℂ) (j : ℕ)
    (d₁ d₂ : ScheduledSymbolData) {T : ℕ} (E : ℝ)
    (I₁ I₂ : Finset ProfileScheduleTest) {L₁ L₂ : ℕ}
    (hL₁ : ∀ test ∈ I₁, test.length ≤ L₁)
    (hL₂ : ∀ test ∈ I₂, test.length ≤ L₂)
    (horder₁ : d₁.order I₁ + p.natDegree ≤ 8 * T)
    (horder₂ : d₂.order I₂ + p.natDegree ≤ 8 * T)
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀) :
    (∑' z : ScheduledPairOperatorBranch p I₁ I₂ × ℕ,
      ‖scheduledPairSeparatedCoefficient p j d₁ d₂ E I₁ I₂ x₀ y₀ ρ z‖) ≤
      polynomialWeightedNorm p
        (scheduledSymbolScale T E I₁ L₁ + scheduledSymbolScale T E I₂ L₂) *
        (Real.sqrt 2 / dist x₀ y₀) ^ j := by
  rw [tsum_norm_scheduledPairSeparatedCoefficient_eq p j d₁ d₂ E I₁ I₂ hρ hsep]
  exact mul_le_mul
    (sum_norm_scheduledPairOperatorBranchCoefficient_le p d₁ d₂ E I₁ I₂ hL₁ hL₂
      horder₁ horder₂)
    (tsum_spatialInversePowerSequenceCoefficient_abs_le j hρ hsep)
    (tsum_nonneg (fun _ ↦ abs_nonneg _))
    (polynomialWeightedNorm_nonneg p (add_nonneg (scheduledSymbolScale_nonneg _ _ _ _)
      (scheduledSymbolScale_nonneg _ _ _ _)))

end FalconerThetaGauge
