module

public import FalconerThetaGauge.ScheduledSymbolOneStep

/-! # Literal finite differentiation trees and the exact coefficient budget in S3 -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical ContDiff

namespace FalconerThetaGauge

/-- A branch records exactly which listed mask was differentiated at each step. -/
def ScheduledSymbolBranch (I : Finset ProfileScheduleTest) : ℕ → Type
  | 0 => Unit
  | j + 1 => ScheduledSymbolBranch I j × {test // test ∈ I}

instance scheduledSymbolBranchFintype (I : Finset ProfileScheduleTest) (j : ℕ) :
    Fintype (ScheduledSymbolBranch I j) := by
  induction j with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ j ih =>
    change Fintype (ScheduledSymbolBranch I j × {test // test ∈ I})
    letI := ih
    infer_instance

def ScheduledSymbolData.branchData (d : ScheduledSymbolData) (I : Finset ProfileScheduleTest) :
    (j : ℕ) → ScheduledSymbolBranch I j → ScheduledSymbolData
  | 0, _ => d
  | j + 1, b => (d.branchData I j b.1).raise b.2.val

def ScheduledSymbolData.branchCoefficient (d : ScheduledSymbolData) (E : ℝ)
    (I : Finset ProfileScheduleTest) : (j : ℕ) → ScheduledSymbolBranch I j → ℝ
  | 0, _ => 1
  | j + 1, b => d.branchCoefficient E I j b.1 *
      scheduledSymbolDerivativeCoefficient E b.2.val
        ((d.branchData I j b.1).derivativeOrders b.2.val)

theorem ScheduledSymbolData.branchData_order (d : ScheduledSymbolData)
    (I : Finset ProfileScheduleTest) (j : ℕ) (b : ScheduledSymbolBranch I j) :
    (d.branchData I j b).order I = d.order I + j := by
  induction j with
  | zero => simp only [ScheduledSymbolData.branchData, Nat.add_zero]
  | succ j ih =>
    rw [ScheduledSymbolData.branchData, ScheduledSymbolData.raise_order _ I b.2.property, ih]
    omega

theorem ScheduledSymbolData.branchData_spatialWeight (d : ScheduledSymbolData)
    (I : Finset ProfileScheduleTest) (j : ℕ) (b : ScheduledSymbolBranch I j) :
    (d.branchData I j b).spatialWeight = d.spatialWeight := by
  induction j with
  | zero => rfl
  | succ j ih => exact ih b.1

/-- The S3 expansion is the literal repeated Leibniz expansion of the actual angular symbol. -/
theorem ScheduledSymbolData.iteratedDeriv_symbol_eq (d : ScheduledSymbolData)
    (ρ : Measure Plane) (E width : ℝ) (K : ℕ) (I : Finset ProfileScheduleTest)
    (j : ℕ) (x : Plane) (θ : ℝ) :
    iteratedDeriv j (fun t ↦ d.symbol ρ E width K I x (unitCircleOfAngle t)) θ =
      ∑ b : ScheduledSymbolBranch I j, d.branchCoefficient E I j b *
        (d.branchData I j b).symbol ρ E width K I x (unitCircleOfAngle θ) := by
  induction j generalizing θ with
  | zero =>
    change d.symbol ρ E width K I x (unitCircleOfAngle θ) =
      ∑ b : Unit, 1 * d.symbol ρ E width K I x (unitCircleOfAngle θ)
    simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv j (fun t ↦ d.symbol ρ E width K I x (unitCircleOfAngle t)) =
        fun t ↦ ∑ b : ScheduledSymbolBranch I j, d.branchCoefficient E I j b *
          (d.branchData I j b).symbol ρ E width K I x (unitCircleOfAngle t) := funext ih
    rw [heq, deriv_fun_sum]
    · change (∑ b : ScheduledSymbolBranch I j, _) =
        ∑ b : ScheduledSymbolBranch I j × {test // test ∈ I}, _
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro b hb
      rw [deriv_const_mul_field, ScheduledSymbolData.deriv_symbol, Finset.mul_sum]
      rw [← Finset.sum_coe_sort I]
      apply Finset.sum_congr rfl
      intro test ht
      simp only [ScheduledSymbolData.branchCoefficient, ScheduledSymbolData.branchData]
      ring
    · intro b hb
      exact (differentiableAt_const (d.branchCoefficient E I j b)).mul
        (((d.branchData I j b).contDiff_symbol_comp_angle ρ E width K I x).differentiable
          (by simp) θ)

/-- The sum of absolute coefficients has exactly the manuscript's `M_L^j` bound. -/
theorem ScheduledSymbolData.sum_abs_branchCoefficients_le (d : ScheduledSymbolData)
    {T : ℕ} (E : ℝ) (I : Finset ProfileScheduleTest) {L : ℕ}
    (hL : ∀ test ∈ I, test.length ≤ L) (j : ℕ) (horder : d.order I + j ≤ 8 * T) :
    ∑ b : ScheduledSymbolBranch I j, |d.branchCoefficient E I j b| ≤
      scheduledSymbolScale T E I L ^ j := by
  induction j with
  | zero =>
    change (∑ _b : Unit, |(1 : ℝ)|) ≤ _ ^ 0
    simp
  | succ j ih =>
    change (∑ b : ScheduledSymbolBranch I j × {test // test ∈ I},
      |d.branchCoefficient E I j b.1 * scheduledSymbolDerivativeCoefficient E b.2.val
        ((d.branchData I j b.1).derivativeOrders b.2.val)|) ≤ _
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ b : ScheduledSymbolBranch I j, |d.branchCoefficient E I j b| *
          ∑ test ∈ I, |scheduledSymbolDerivativeCoefficient E test
            ((d.branchData I j b).derivativeOrders test)| := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [← Finset.sum_coe_sort I, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro test ht
        exact abs_mul _ _
      _ ≤ ∑ b : ScheduledSymbolBranch I j, |d.branchCoefficient E I j b| *
          scheduledSymbolScale T E I L := by
        apply Finset.sum_le_sum
        intro b hb
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply ScheduledSymbolData.sum_abs_derivativeCoefficients_le _ E I hL
        rw [d.branchData_order]
        omega
      _ = (∑ b : ScheduledSymbolBranch I j, |d.branchCoefficient E I j b|) *
          scheduledSymbolScale T E I L := (Finset.sum_mul _ _ _).symm
      _ ≤ scheduledSymbolScale T E I L ^ j * scheduledSymbolScale T E I L :=
        mul_le_mul_of_nonneg_right (ih (by omega)) (scheduledSymbolScale_nonneg T E I L)
      _ = scheduledSymbolScale T E I L ^ (j + 1) := (pow_succ _ _).symm

/-- Each term belongs to the concrete next-order class, with the same Borel spatial weight. -/
theorem ScheduledSymbolData.branch_symbol_mem (d : ScheduledSymbolData)
    (ρ : Measure Plane) (E width : ℝ) (K : ℕ) (I : Finset ProfileScheduleTest)
    {k₀ : ℕ} (horder : d.order I ≤ k₀) (j : ℕ) (b : ScheduledSymbolBranch I j) :
    (d.branchData I j b).symbol ρ E width K I ∈
      scheduledSymbolClass ρ E width K I (k₀ + j) := by
  refine ⟨d.branchData I j b, ?_, rfl⟩
  rw [d.branchData_order]
  omega

end FalconerThetaGauge
