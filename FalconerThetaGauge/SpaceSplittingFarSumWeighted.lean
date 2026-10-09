/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.SpaceSplittingFarSum
public import FalconerThetaGauge.SpaceSplittingIntegratedKernel

/-! # Actual far kernel integration, with true distance weights and true passing sets -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical ENNReal

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem spaceSplittingFarCrossSum_le_lintegral_majorant (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {a p : ℕ} (hap : a ≤ p)
    (X Y : Fin 2 → ℤ) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂))
    (hbound₁ : ∀ x w, |b₁ x w| ≤ 1) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    (K v : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    {f : (Plane × Plane) × (Plane × Plane) → ℝ≥0∞} (hf : Measurable f)
    (hfin : (∫⁻ z, f z ∂spaceSplittingRootFourMeasure ρ a X Y) ≠ ⊤)
    (hmajor : ∀ P ∈ spaceSplittingFinePairs ρ a p X Y,
      ∀ Q ∈ spaceSplittingFinePairs ρ a p X Y, ¬spaceSplittingNear p P Q →
        ∀ x ∈ dyadicCube p P.1, ∀ x' ∈ dyadicCube p Q.1,
          ∀ y ∈ dyadicCube p P.2, ∀ y' ∈ dyadicCube p Q.2,
            ‖spaceSplittingAveragedCircleKernel b₁ b₂ K v x x' y y'‖ ≤
              δ + (f ((x, x'), (y, y'))).toReal) :
    spaceSplittingFarCrossSum ρ a p X Y b₁ b₂ K v ≤
      δ * (ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y)) ^ 2 +
        (∫⁻ z, f z ∂spaceSplittingRootFourMeasure ρ a X Y).toReal := by
  have hh := spaceSplittingFarCrossSum_le_majorant ρ hρ hap X Y hb₁ hb₂ hbound₁ hbound₂
    K v hδ (integrable_toReal_of_lintegral_ne_top hf.aemeasurable hfin)
    (fun _ ↦ ENNReal.toReal_nonneg) hmajor
  rwa [integral_toReal hf.aemeasurable (ae_lt_top hf hfin)] at hh

theorem spaceSplittingFarWeightedKernel_lintegral_ne_top (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) (a p : ℕ) (X Y : Fin 2 → ℤ)
    {Z : Set (Plane × Plane)} (hZ : MeasurableSet Z) (v : ℕ) :
    (∫⁻ z, spaceSplittingWeightedKernel ((2 : ℝ) ^ (-(v : ℝ))) Z Z z
      ∂(spaceSplittingRootFourMeasure ρ a X Y).restrict
        (spaceSplittingFarComparableSet p)) ≠ ⊤ := by
  have hh := lintegral_spaceSplittingFarComparable_le_depth_sum ρ hρ a p X Y
    (spaceSplittingWeightedKernel ((2 : ℝ) ^ (-(v : ℝ))) Z Z)
  change _ ≤ ∑ n ∈ Finset.Ioo a (p + 12), spaceSplittingDepthKernelSum ρ a n X Y Z v at hh
  exact ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 (fun n _ ↦
    spaceSplittingDepthKernelSum_ne_top ρ a n X Y hZ v)) hh

theorem spaceSplittingFarCrossSum_le_weighted_kernel (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {a p : ℕ} (hap : a ≤ p)
    (X Y : Fin 2 → ℤ) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂))
    (hbound₁ : ∀ x w, |b₁ x w| ≤ 1) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    (K v : ℕ) {δ C : ℝ} (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    {Z : Set (Plane × Plane)} (hZ : MeasurableSet Z)
    (hmajor : ∀ P ∈ spaceSplittingFinePairs ρ a p X Y,
      ∀ Q ∈ spaceSplittingFinePairs ρ a p X Y, ¬spaceSplittingNear p P Q →
        ∀ x ∈ dyadicCube p P.1, ∀ x' ∈ dyadicCube p Q.1,
          ∀ y ∈ dyadicCube p P.2, ∀ y' ∈ dyadicCube p Q.2,
            ‖spaceSplittingAveragedCircleKernel b₁ b₂ K v x x' y y'‖ ≤
              δ + C * (spaceSplittingFarComparableSet p).indicator (fun z ↦
                (spaceSplittingWeightedKernel ((2 : ℝ) ^ (-(v : ℝ))) Z Z z).toReal)
                ((x, x'), (y, y'))) :
    spaceSplittingFarCrossSum ρ a p X Y b₁ b₂ K v ≤
      δ * (ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y)) ^ 2 +
        C * (∫⁻ z, spaceSplittingWeightedKernel ((2 : ℝ) ^ (-(v : ℝ))) Z Z z
          ∂(spaceSplittingRootFourMeasure ρ a X Y).restrict
            (spaceSplittingFarComparableSet p)).toReal := by
  let f := fun z ↦ ENNReal.ofReal C * (spaceSplittingFarComparableSet p).indicator
    (spaceSplittingWeightedKernel ((2 : ℝ) ^ (-(v : ℝ))) Z Z) z
  have hf : Measurable f := measurable_const.mul
    ((measurable_spaceSplittingWeightedKernel _ hZ hZ).indicator
      (measurableSet_spaceSplittingFarComparableSet p))
  have he : (∫⁻ z, f z ∂spaceSplittingRootFourMeasure ρ a X Y) =
      ENNReal.ofReal C * (∫⁻ z, spaceSplittingWeightedKernel ((2 : ℝ) ^ (-(v : ℝ))) Z Z z
        ∂(spaceSplittingRootFourMeasure ρ a X Y).restrict
          (spaceSplittingFarComparableSet p)) := by
    rw [lintegral_const_mul _ _]
    rw [lintegral_indicator (measurableSet_spaceSplittingFarComparableSet p)]
    exact (measurable_spaceSplittingWeightedKernel _ hZ hZ).indicator
      (measurableSet_spaceSplittingFarComparableSet p)
  have hfin : (∫⁻ z, f z ∂spaceSplittingRootFourMeasure ρ a X Y) ≠ ⊤ := by
    rw [he]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (spaceSplittingFarWeightedKernel_lintegral_ne_top ρ hρ a p X Y hZ v)
  have hfval (z : (Plane × Plane) × (Plane × Plane)) :
      (f z).toReal = C * (spaceSplittingFarComparableSet p).indicator (fun z ↦
        (spaceSplittingWeightedKernel ((2 : ℝ) ^ (-(v : ℝ))) Z Z z).toReal) z := by
    simp only [f, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC]
    by_cases hz : z ∈ spaceSplittingFarComparableSet p <;> simp [hz]
  have hh := spaceSplittingFarCrossSum_le_lintegral_majorant ρ hρ hap X Y
    hb₁ hb₂ hbound₁ hbound₂ K v hδ hf hfin (by simpa only [hfval] using hmajor)
  rwa [he, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] at hh

end FalconerThetaGauge
