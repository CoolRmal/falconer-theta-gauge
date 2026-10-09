/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierSeparationPolynomialSymbols
public import FalconerThetaGauge.MaskedDistanceEnergyFourier
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Genuine separated inverse powers under the spatial and circle integrals -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric

namespace FalconerThetaGauge

def separatedInversePowerKernelTerm (j : ℕ) (x₀ y₀ : Plane) (ρ : ℝ)
    (X Y : Set Plane) (b₁ b₂ : Plane → UnitCircle → ℝ) (ψ : UnitCircle → ℝ)
    (r : ℝ) (n : ℕ) (p : UnitCircle × (Plane × Plane)) : ℂ :=
  (spatialInversePowerSequenceCoefficient j x₀ y₀ ρ n : ℂ) * (ψ p.1 : ℂ) *
    maskedFourierPairKernel
      (carrierPolynomialSymbol X (spatialInversePowerSequenceLeftPolynomial x₀ ρ n) b₁)
      (carrierPolynomialSymbol Y (spatialInversePowerSequenceRightPolynomial y₀ ρ n) b₂)
      r p.1 p.2

def inversePowerCircleKernel (j : ℕ) (b₁ b₂ : Plane → UnitCircle → ℝ)
    (ψ : UnitCircle → ℝ) (r : ℝ) (p : UnitCircle × (Plane × Plane)) : ℂ :=
  ((dist p.2.1 p.2.2)⁻¹ ^ j : ℝ) *
    ((ψ p.1 : ℂ) * maskedFourierPairKernel b₁ b₂ r p.1 p.2)

theorem hasSum_separatedInversePowerKernelTerm (j : ℕ) {x₀ y₀ : Plane} {ρ : ℝ}
    (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀) {X Y : Set Plane}
    (hXball : X ⊆ closedBall x₀ ρ) (hYball : Y ⊆ closedBall y₀ ρ)
    (b₁ b₂ : Plane → UnitCircle → ℝ) (ψ : UnitCircle → ℝ) (r : ℝ)
    (p : UnitCircle × (Plane × Plane)) (hp : p.2.1 ∈ X ∧ p.2.2 ∈ Y) :
    HasSum (fun n ↦ separatedInversePowerKernelTerm j x₀ y₀ ρ X Y b₁ b₂ ψ r n p)
      (inversePowerCircleKernel j b₁ b₂ ψ r p) := by
  have hs := Complex.hasSum_ofReal.mpr (hasSum_spatialInversePowerSequenceTerm
    j hρ hsep (hXball hp.1) (hYball hp.2))
  have hm := hs.mul_right ((ψ p.1 : ℂ) * maskedFourierPairKernel b₁ b₂ r p.1 p.2)
  convert hm using 1
  · funext n
    simp only [separatedInversePowerKernelTerm, spatialInversePowerSequenceTerm_eq,
      maskedFourierPairKernel,
      carrierPolynomialSymbol_eq_on_carrier _ _ hp.1,
      carrierPolynomialSymbol_eq_on_carrier _ _ hp.2, Complex.ofReal_mul]
    ring
  · rfl

@[fun_prop]
theorem measurable_inversePowerCircleKernel (j : ℕ)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) {ψ : UnitCircle → ℝ} (hψ : Measurable ψ) (r : ℝ) :
    Measurable (inversePowerCircleKernel j b₁ b₂ ψ r) := by
  have hd : Measurable (fun p : UnitCircle × (Plane × Plane) ↦
      ((dist p.2.1 p.2.2)⁻¹ ^ j : ℝ)) := by fun_prop
  exact hd.complex_ofReal.mul (((hψ.comp measurable_fst).complex_ofReal).mul
    (measurable_maskedFourierPairKernel hb₁ hb₂ r))

theorem norm_separatedInversePowerKernelTerm_le (j : ℕ) {x₀ y₀ : Plane} {ρ : ℝ}
    (hρ : 0 < ρ) {X Y : Set Plane} (hXball : X ⊆ closedBall x₀ ρ)
    (hYball : Y ⊆ closedBall y₀ ρ) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hbound₁ : ∀ x w, |b₁ x w| ≤ 1) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    {ψ : UnitCircle → ℝ} (hψ₁ : ∀ w, |ψ w| ≤ 1) (r : ℝ) (n : ℕ)
    (p : UnitCircle × (Plane × Plane)) :
    ‖separatedInversePowerKernelTerm j x₀ y₀ ρ X Y b₁ b₂ ψ r n p‖ ≤
      |spatialInversePowerSequenceCoefficient j x₀ y₀ ρ n| := by
  have hb₁ := abs_carrierPolynomialSymbol_le_one _
    (fun x hx ↦ abs_eval_spatialInversePowerSequenceLeftPolynomial_le_one hρ (hXball hx) n)
    hbound₁ p.2.1 p.1
  have hb₂ := abs_carrierPolynomialSymbol_le_one _
    (fun y hy ↦ abs_eval_spatialInversePowerSequenceRightPolynomial_le_one hρ (hYball hy) n)
    hbound₂ p.2.2 p.1
  rw [separatedInversePowerKernelTerm, norm_mul, norm_mul, norm_maskedFourierPairKernel,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  calc
    _ ≤ |spatialInversePowerSequenceCoefficient j x₀ y₀ ρ n| * 1 * (1 * 1) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hψ₁ _) (abs_nonneg _))
        (mul_le_mul hb₁ hb₂ (abs_nonneg _) (by norm_num))
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity)
    _ = _ := by ring

theorem hasSum_integral_separatedInversePowerKernelTerm (j : ℕ)
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    {X Y : Set Plane} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hXball : X ⊆ closedBall x₀ ρ) (hYball : Y ⊆ closedBall y₀ ρ)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) {ψ : UnitCircle → ℝ}
    (hψ : Measurable ψ) (hψ₁ : ∀ w, |ψ w| ≤ 1) (r : ℝ) :
    HasSum (fun n ↦ ∫ p, separatedInversePowerKernelTerm j x₀ y₀ ρ X Y b₁ b₂ ψ r n p
      ∂circleArcLength.prod ((ρ₁.restrict X).prod (ρ₂.restrict Y)))
      (∫ p, inversePowerCircleKernel j b₁ b₂ ψ r p
        ∂circleArcLength.prod ((ρ₁.restrict X).prod (ρ₂.restrict Y))) := by
  have hs := summable_spatialInversePowerSequenceCoefficient_abs j hρ hsep
  apply hasSum_integral_of_dominated_convergence
    (fun n (_p : UnitCircle × (Plane × Plane)) ↦
      |spatialInversePowerSequenceCoefficient j x₀ y₀ ρ n|)
  · intro n
    exact ((measurable_const.mul (hψ.comp measurable_fst).complex_ofReal).mul
      (measurable_maskedFourierPairKernel
        (measurable_carrierPolynomialSymbol hX _ hb₁)
        (measurable_carrierPolynomialSymbol hY _ hb₂) r)).aestronglyMeasurable
  · intro n
    exact Eventually.of_forall
      (norm_separatedInversePowerKernelTerm_le j hρ hXball hYball hbound₁ hbound₂ hψ₁ r n)
  · exact Eventually.of_forall (fun _ ↦ hs)
  · exact integrable_const _
  · filter_upwards [Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually
      (ae_restricted_product_carriers ρ₁ ρ₂ hX hY)] with p hp
    exact hasSum_separatedInversePowerKernelTerm j hρ hsep hXball hYball b₁ b₂ ψ r p hp

end FalconerThetaGauge
