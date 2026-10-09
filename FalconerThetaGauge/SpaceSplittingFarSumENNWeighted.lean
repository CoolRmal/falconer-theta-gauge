/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.SpaceSplittingFarSumENNBound
public import FalconerThetaGauge.SpaceSplittingFarKernel

/-! # Literal ENNReal averaged-kernel estimates imply the genuine finite far energy bound -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical ENNReal

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem spaceSplittingFarCrossSum_le_distance_maxima_of_ofReal_bound
    (ρ : Measure Plane) [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1)
    {a p : ℕ} (hap : a ≤ p) (X Y : Fin 2 → ℤ) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂))
    (hbound₁ : ∀ x w, |b₁ x w| ≤ 1) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    (K v : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) {Z : Set (Plane × Plane)} (hZ : MeasurableSet Z)
    (hmajor : ∀ P ∈ spaceSplittingFinePairs ρ a p X Y,
      ∀ Q ∈ spaceSplittingFinePairs ρ a p X Y, ¬spaceSplittingNear p P Q →
        ∀ x ∈ dyadicCube p P.1, ∀ x' ∈ dyadicCube p Q.1,
          ∀ y ∈ dyadicCube p P.2, ∀ y' ∈ dyadicCube p Q.2,
            ENNReal.ofReal ‖spaceSplittingAveragedCircleKernel b₁ b₂ K v x x' y y'‖ ≤
              ENNReal.ofReal ((2 : ℝ) ^ (25 : ℕ)) * ENNReal.ofReal ((2 : ℝ) ^ v) *
                spaceSplittingFarWeightedKernel p v Z Z ((x, x'), (y, y')) +
                  ENNReal.ofReal δ) :
    spaceSplittingFarCrossSum ρ a p X Y b₁ b₂ K v ≤
      δ * (ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y)) ^ 2 +
        (2 : ℝ) ^ (90 : ℕ) * ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y) *
          ∑ n ∈ Finset.Ioo a (p + 12), spaceSplittingDistanceMaximum ρ a n X Y Z v := by
  let C := ENNReal.ofReal ((2 : ℝ) ^ (25 : ℕ)) * ENNReal.ofReal ((2 : ℝ) ^ v)
  let f := fun z ↦ C * spaceSplittingFarWeightedKernel p v Z Z z
  have hf : Measurable f := measurable_const.mul
    (measurable_spaceSplittingFarWeightedKernel p v hZ hZ)
  have hC : C ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have he : (∫⁻ z, f z ∂spaceSplittingRootFourMeasure ρ a X Y) =
      C * (∫⁻ z, spaceSplittingWeightedKernel ((2 : ℝ) ^ (-(v : ℝ))) Z Z z
        ∂(spaceSplittingRootFourMeasure ρ a X Y).restrict
          (spaceSplittingFarComparableSet p)) := by
    rw [lintegral_const_mul _ (measurable_spaceSplittingFarWeightedKernel p v hZ hZ)]
    rw [spaceSplittingFarWeightedKernel,
      lintegral_indicator (measurableSet_spaceSplittingFarComparableSet p)]
  have hfin : (∫⁻ z, f z ∂spaceSplittingRootFourMeasure ρ a X Y) ≠ ⊤ := by
    rw [he]
    exact ENNReal.mul_ne_top hC
      (spaceSplittingFarWeightedKernel_lintegral_ne_top ρ hρ a p X Y hZ v)
  have hh := spaceSplittingFarCrossSum_le_of_ofReal_majorant ρ hρ hap X Y hb₁ hb₂
    hbound₁ hbound₂ K v hδ hf hfin (by simpa only [f, C, add_comm] using hmajor)
  rw [he, ENNReal.toReal_mul] at hh
  have hCval : C.toReal = (2 : ℝ) ^ (25 : ℕ) * (2 : ℝ) ^ v := by
    dsimp only [C]
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 2 ^ (25 : ℕ) by positivity),
      ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 2 ^ v by positivity)]
  rw [hCval] at hh
  exact hh.trans (add_le_add le_rfl
    (spaceSplitting_far_kernel_toReal_le ρ hρ a p X Y hZ v))

end FalconerThetaGauge
