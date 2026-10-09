/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierSeparationBilinear
public import FalconerThetaGauge.ScheduledSymbolExpansion
public import FalconerThetaGauge.StationaryPhaseInverseOperatorsAction

/-! # Actual angular derivative products expanded into literal scheduled symbols -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped ContDiff

namespace FalconerThetaGauge

theorem contDiff_iteratedDeriv_real_infty {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n f) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ n ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.mp ih).2

theorem iteratedDeriv_complex_ofReal {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    iteratedDeriv n (fun t ↦ (f t : ℂ)) = fun t ↦ ((iteratedDeriv n f t : ℝ) : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    funext x
    exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
      ((contDiff_iteratedDeriv_real_infty hf n).differentiable (by simp) x).hasDerivAt).deriv

theorem ScheduledSymbolData.iteratedDeriv_complex_symbol_eq (d : ScheduledSymbolData)
    (ρ : Measure Plane) (E width : ℝ) (K : ℕ) (I : Finset ProfileScheduleTest)
    (j : ℕ) (x : Plane) (θ : ℝ) :
    iteratedDeriv j (fun t ↦ (d.symbol ρ E width K I x (unitCircleOfAngle t) : ℂ)) θ =
      ∑ b : ScheduledSymbolBranch I j, (d.branchCoefficient E I j b : ℂ) *
        ((d.branchData I j b).symbol ρ E width K I x (unitCircleOfAngle θ) : ℂ) := by
  rw [iteratedDeriv_complex_ofReal (d.contDiff_symbol_comp_angle ρ E width K I x)]
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul] using congrArg
    (fun a : ℝ ↦ (a : ℂ)) (d.iteratedDeriv_symbol_eq ρ E width K I j x θ)

theorem scheduledSymbolPair_iteratedDeriv_eq (d₁ d₂ : ScheduledSymbolData)
    (ρ₁ ρ₂ : Measure Plane) (E width : ℝ) (K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest)
    (l : ℕ) (x y : Plane) (θ : ℝ) :
    iteratedDeriv l (fun t ↦ (d₁.symbol ρ₁ E width K I₁ x (unitCircleOfAngle t) : ℂ) *
      (d₂.symbol ρ₂ E width K I₂ y (unitCircleOfAngle t) : ℂ)) θ =
      ∑ s ∈ range (l + 1), ∑ b₁ : ScheduledSymbolBranch I₁ s,
        ∑ b₂ : ScheduledSymbolBranch I₂ (l - s),
          ((l.choose s : ℂ) * (d₁.branchCoefficient E I₁ s b₁ : ℂ) *
            (d₂.branchCoefficient E I₂ (l - s) b₂ : ℂ)) *
          ((d₁.branchData I₁ s b₁).symbol ρ₁ E width K I₁ x
            (unitCircleOfAngle θ) : ℂ) *
          ((d₂.branchData I₂ (l - s) b₂).symbol ρ₂ E width K I₂ y
            (unitCircleOfAngle θ) : ℂ) := by
  have hf₁ : ContDiff ℝ ∞
      (fun t ↦ (d₁.symbol ρ₁ E width K I₁ x (unitCircleOfAngle t) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (d₁.contDiff_symbol_comp_angle ρ₁ E width K I₁ x)
  have hf₂ : ContDiff ℝ ∞
      (fun t ↦ (d₂.symbol ρ₂ E width K I₂ y (unitCircleOfAngle t) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (d₂.contDiff_symbol_comp_angle ρ₂ E width K I₂ y)
  rw [iteratedDeriv_fun_mul
    (hf₁.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop (le_refl ∞) l))
    (hf₂.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop (le_refl ∞) l))]
  simp_rw [ScheduledSymbolData.iteratedDeriv_complex_symbol_eq, mul_sum, sum_mul]
  apply sum_congr rfl
  intro s _
  rw [sum_comm]
  apply sum_congr rfl
  intro b₁ _
  apply sum_congr rfl
  intro b₂ _
  ring

end FalconerThetaGauge
