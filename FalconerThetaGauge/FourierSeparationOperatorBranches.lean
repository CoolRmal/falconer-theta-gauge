/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierSeparationLeibnizBudget

/-! # The actual finite branch index of a polynomial inverse operator -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset Polynomial
open scoped Classical ContDiff

namespace FalconerThetaGauge

def ScheduledPairOperatorBranch (p : Polynomial ℂ)
    (I₁ I₂ : Finset ProfileScheduleTest) :=
  Σ l : {l // l ∈ p.support}, Σ s : {s // s ∈ range (l.val + 1)},
    ScheduledSymbolBranch I₁ s.val × ScheduledSymbolBranch I₂ (l.val - s.val)

instance (p : Polynomial ℂ) (I₁ I₂ : Finset ProfileScheduleTest) :
    Fintype (ScheduledPairOperatorBranch p I₁ I₂) := by
  unfold ScheduledPairOperatorBranch
  infer_instance

theorem sum_scheduledPairOperatorBranch {A : Type*} [AddCommMonoid A]
    (p : Polynomial ℂ) (I₁ I₂ : Finset ProfileScheduleTest)
    (f : (l s : ℕ) → ScheduledSymbolBranch I₁ s →
      ScheduledSymbolBranch I₂ (l - s) → A) :
    (∑ b : ScheduledPairOperatorBranch p I₁ I₂,
      f b.1.val b.2.1.val b.2.2.1 b.2.2.2) =
      ∑ l ∈ p.support, ∑ s ∈ range (l + 1), ∑ b₁ : ScheduledSymbolBranch I₁ s,
        ∑ b₂ : ScheduledSymbolBranch I₂ (l - s), f l s b₁ b₂ := by
  unfold ScheduledPairOperatorBranch
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
  rw [sum_coe_sort p.support (fun l ↦ ∑ s : {s // s ∈ Finset.range (l + 1)},
    ∑ b₁ : ScheduledSymbolBranch I₁ s.val,
      ∑ b₂ : ScheduledSymbolBranch I₂ (l - s.val), f l s.val b₁ b₂)]
  apply sum_congr rfl
  intro l _
  exact sum_coe_sort (Finset.range (l + 1)) (fun s ↦ ∑ b₁ : ScheduledSymbolBranch I₁ s,
    ∑ b₂ : ScheduledSymbolBranch I₂ (l - s), f l s b₁ b₂)

def scheduledPairOperatorBranchCoefficient (p : Polynomial ℂ) (d₁ d₂ : ScheduledSymbolData)
    (E : ℝ) (I₁ I₂ : Finset ProfileScheduleTest)
    (b : ScheduledPairOperatorBranch p I₁ I₂) : ℂ :=
  p.coeff b.1.val * (b.1.val.choose b.2.1.val : ℂ) *
    (d₁.branchCoefficient E I₁ b.2.1.val b.2.2.1 : ℂ) *
    (d₂.branchCoefficient E I₂ (b.1.val - b.2.1.val) b.2.2.2 : ℂ)

def scheduledPairOperatorLeftData (p : Polynomial ℂ) (d : ScheduledSymbolData)
    (I₁ I₂ : Finset ProfileScheduleTest) (b : ScheduledPairOperatorBranch p I₁ I₂) :
    ScheduledSymbolData := d.branchData I₁ b.2.1.val b.2.2.1

def scheduledPairOperatorRightData (p : Polynomial ℂ) (d : ScheduledSymbolData)
    (I₁ I₂ : Finset ProfileScheduleTest) (b : ScheduledPairOperatorBranch p I₁ I₂) :
    ScheduledSymbolData := d.branchData I₂ (b.1.val - b.2.1.val) b.2.2.2

theorem scheduledPairOperatorLeftData_order_le (p : Polynomial ℂ) (d : ScheduledSymbolData)
    (I₁ I₂ : Finset ProfileScheduleTest) (b : ScheduledPairOperatorBranch p I₁ I₂) :
    (scheduledPairOperatorLeftData p d I₁ I₂ b).order I₁ ≤ d.order I₁ + p.natDegree := by
  have hl := le_natDegree_of_ne_zero (mem_support_iff.mp b.1.property)
  have hs : b.2.1.val ≤ b.1.val := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using b.2.1.property
  simp only [scheduledPairOperatorLeftData, ScheduledSymbolData.branchData_order]
  omega

theorem scheduledPairOperatorRightData_order_le (p : Polynomial ℂ) (d : ScheduledSymbolData)
    (I₁ I₂ : Finset ProfileScheduleTest) (b : ScheduledPairOperatorBranch p I₁ I₂) :
    (scheduledPairOperatorRightData p d I₁ I₂ b).order I₂ ≤ d.order I₂ + p.natDegree := by
  have hl := le_natDegree_of_ne_zero (mem_support_iff.mp b.1.property)
  simp only [scheduledPairOperatorRightData, ScheduledSymbolData.branchData_order]
  omega

theorem polynomialDifferentialAction_scheduledPairOperator_eq (p : Polynomial ℂ)
    (d₁ d₂ : ScheduledSymbolData) (ρ₁ ρ₂ : Measure Plane) (E width : ℝ) (K : ℕ)
    (I₁ I₂ : Finset ProfileScheduleTest) (x y : Plane) (θ : ℝ) :
    polynomialDifferentialAction p
      (fun t ↦ (d₁.symbol ρ₁ E width K I₁ x (unitCircleOfAngle t) : ℂ) *
        (d₂.symbol ρ₂ E width K I₂ y (unitCircleOfAngle t) : ℂ)) θ =
      ∑ b : ScheduledPairOperatorBranch p I₁ I₂,
        scheduledPairOperatorBranchCoefficient p d₁ d₂ E I₁ I₂ b *
        ((scheduledPairOperatorLeftData p d₁ I₁ I₂ b).symbol
          ρ₁ E width K I₁ x (unitCircleOfAngle θ) : ℂ) *
        ((scheduledPairOperatorRightData p d₂ I₁ I₂ b).symbol
          ρ₂ E width K I₂ y (unitCircleOfAngle θ) : ℂ) := by
  refine (polynomialDifferentialAction_scheduledSymbolPair_eq p d₁ d₂
    ρ₁ ρ₂ E width K I₁ I₂ x y θ).trans ?_
  exact (sum_scheduledPairOperatorBranch p I₁ I₂ (fun l s b₁ b₂ ↦
    (p.coeff l * (l.choose s : ℂ) * (d₁.branchCoefficient E I₁ s b₁ : ℂ) *
      (d₂.branchCoefficient E I₂ (l - s) b₂ : ℂ)) *
    ((d₁.branchData I₁ s b₁).symbol ρ₁ E width K I₁ x (unitCircleOfAngle θ) : ℂ) *
    ((d₂.branchData I₂ (l - s) b₂).symbol
      ρ₂ E width K I₂ y (unitCircleOfAngle θ) : ℂ))).symm

theorem sum_norm_scheduledPairOperatorBranchCoefficient_le (p : Polynomial ℂ)
    (d₁ d₂ : ScheduledSymbolData) {T : ℕ} (E : ℝ)
    (I₁ I₂ : Finset ProfileScheduleTest) {L₁ L₂ : ℕ}
    (hL₁ : ∀ test ∈ I₁, test.length ≤ L₁)
    (hL₂ : ∀ test ∈ I₂, test.length ≤ L₂)
    (horder₁ : d₁.order I₁ + p.natDegree ≤ 8 * T)
    (horder₂ : d₂.order I₂ + p.natDegree ≤ 8 * T) :
    (∑ b : ScheduledPairOperatorBranch p I₁ I₂,
      ‖scheduledPairOperatorBranchCoefficient p d₁ d₂ E I₁ I₂ b‖) ≤
      polynomialWeightedNorm p
        (scheduledSymbolScale T E I₁ L₁ + scheduledSymbolScale T E I₂ L₂) := by
  calc
    _ = ∑ l ∈ p.support, ∑ s ∈ range (l + 1), ∑ b₁ : ScheduledSymbolBranch I₁ s,
        ∑ b₂ : ScheduledSymbolBranch I₂ (l - s),
          ‖p.coeff l * (l.choose s : ℂ) * (d₁.branchCoefficient E I₁ s b₁ : ℂ) *
            (d₂.branchCoefficient E I₂ (l - s) b₂ : ℂ)‖ :=
      sum_scheduledPairOperatorBranch p I₁ I₂ (fun l s b₁ b₂ ↦
        ‖p.coeff l * (l.choose s : ℂ) * (d₁.branchCoefficient E I₁ s b₁ : ℂ) *
          (d₂.branchCoefficient E I₂ (l - s) b₂ : ℂ)‖)
    _ ≤ _ := sum_norm_scheduledSymbolPair_operator_coefficients_le p d₁ d₂ E I₁ I₂
      hL₁ hL₂ horder₁ horder₂

end FalconerThetaGauge
