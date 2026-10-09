/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.SpaceSplittingFarSumMeasures

/-! # Genuine far cross-term summation retains the root four-point measure -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical RealInnerProductSpace

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

def spaceSplittingFarCrossSum (ρ : Measure Plane) (a p : ℕ) (X Y : Fin 2 → ℤ)
    (b₁ b₂ : Plane → UnitCircle → ℝ) (K v : ℕ) : ℝ :=
  ∑ P ∈ spaceSplittingFinePairs ρ a p X Y,
    ∑ Q ∈ spaceSplittingFinePairs ρ a p X Y,
      if spaceSplittingNear p P Q then 0 else
        |∫ z, inner ℝ
          (spaceSplittingJointAmplitude ρ ρ (dyadicCube p P.1) (dyadicCube p P.2) b₁ b₂ z)
          (spaceSplittingJointAmplitude ρ ρ (dyadicCube p Q.1) (dyadicCube p Q.2) b₁ b₂ z)
          ∂maskedFourierJointMeasure K v|

theorem spaceSplittingRootFourMeasure_real_univ (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (a : ℕ) (X Y : Fin 2 → ℤ) :
    (spaceSplittingRootFourMeasure ρ a X Y).real univ =
      (ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y)) ^ 2 := by
  have hm (μ ν : Measure (Plane × Plane)) [SFinite ν] :
      (μ.prod ν).real univ = μ.real univ * ν.real univ := by
    simpa only [univ_prod_univ] using measureReal_prod_prod (μ := μ) (ν := ν) univ univ
  have hm' (μ ν : Measure Plane) [SFinite ν] :
      (μ.prod ν).real univ = μ.real univ * ν.real univ := by
    simpa only [univ_prod_univ] using measureReal_prod_prod (μ := μ) (ν := ν) univ univ
  rw [spaceSplittingRootFourMeasure, hm, hm', hm']
  simp only [Measure.real, Measure.restrict_apply_univ]
  ring

/-- A literal pointwise majorant on each true far cell is integrated and regrouped exactly. -/
theorem spaceSplittingFarCrossSum_le_majorant (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {a p : ℕ} (hap : a ≤ p)
    (X Y : Fin 2 → ℤ) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂))
    (hbound₁ : ∀ x w, |b₁ x w| ≤ 1) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    (K v : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    {f : (Plane × Plane) × (Plane × Plane) → ℝ}
    (hf : Integrable f (spaceSplittingRootFourMeasure ρ a X Y)) (hf₀ : ∀ z, 0 ≤ f z)
    (hmajor : ∀ P ∈ spaceSplittingFinePairs ρ a p X Y,
      ∀ Q ∈ spaceSplittingFinePairs ρ a p X Y, ¬spaceSplittingNear p P Q →
        ∀ x ∈ dyadicCube p P.1, ∀ x' ∈ dyadicCube p Q.1,
          ∀ y ∈ dyadicCube p P.2, ∀ y' ∈ dyadicCube p Q.2,
            ‖spaceSplittingAveragedCircleKernel b₁ b₂ K v x x' y y'‖ ≤
              δ + f ((x, x'), (y, y'))) :
    spaceSplittingFarCrossSum ρ a p X Y b₁ b₂ K v ≤
      δ * (ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y)) ^ 2 +
        ∫ z, f z ∂spaceSplittingRootFourMeasure ρ a X Y := by
  have hfi := (integrable_const δ).add hf
  have hterm (P : (Fin 2 → ℤ) × (Fin 2 → ℤ))
      (hP : P ∈ spaceSplittingFinePairs ρ a p X Y)
      (Q : (Fin 2 → ℤ) × (Fin 2 → ℤ))
      (hQ : Q ∈ spaceSplittingFinePairs ρ a p X Y) :
      (if spaceSplittingNear p P Q then 0 else
        |∫ z, inner ℝ
          (spaceSplittingJointAmplitude ρ ρ (dyadicCube p P.1) (dyadicCube p P.2) b₁ b₂ z)
          (spaceSplittingJointAmplitude ρ ρ (dyadicCube p Q.1) (dyadicCube p Q.2) b₁ b₂ z)
          ∂maskedFourierJointMeasure K v|) ≤
      ∫ z, δ + f z ∂spaceSplittingFineFourMeasure ρ p P Q := by
    by_cases hn : spaceSplittingNear p P Q
    · rw [ite_eq_left hn]
      exact integral_nonneg (fun z ↦ add_nonneg hδ (hf₀ z))
    · rw [ite_eq_right hn]
      apply (abs_integral_spaceSplittingJointAmplitude_inner_le_integral_norm ρ ρ
        (dyadicCube p P.1) (dyadicCube p Q.1) (dyadicCube p P.2) (dyadicCube p Q.2)
        K v hb₁ hb₂ hbound₁ hbound₂).trans
      apply integral_mono_ae
        (integrable_spaceSplittingAveragedCircleKernel (spaceSplittingFineFourMeasure ρ p P Q)
          hb₁ hb₂ hbound₁ hbound₂ K v).norm
        (integrable_spaceSplittingFineFourMeasure ρ hρ hap X Y hfi hP hQ)
      have hae := ae_mem_four_carriers ρ ρ (measurableSet_dyadicCube p P.1)
        (measurableSet_dyadicCube p Q.1) (measurableSet_dyadicCube p P.2)
        (measurableSet_dyadicCube p Q.2)
      filter_upwards [hae] with z hz
      exact hmajor P hP Q hQ hn z.1.1 hz.1.1 z.1.2 hz.1.2 z.2.1 hz.2.1 z.2.2 hz.2.2
  calc
    _ ≤ ∑ P ∈ spaceSplittingFinePairs ρ a p X Y,
        ∑ Q ∈ spaceSplittingFinePairs ρ a p X Y,
          ∫ z, δ + f z ∂spaceSplittingFineFourMeasure ρ p P Q := by
      exact sum_le_sum (fun P hP ↦ sum_le_sum (fun Q hQ ↦ hterm P hP Q hQ))
    _ = ∫ z, δ + f z ∂spaceSplittingRootFourMeasure ρ a X Y :=
      sum_integral_spaceSplittingFineFourMeasure ρ hρ hap X Y hfi
    _ = _ := by
      rw [integral_add (integrable_const δ) hf, integral_const,
        spaceSplittingRootFourMeasure_real_univ, smul_eq_mul, mul_comm]

end FalconerThetaGauge
