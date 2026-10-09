/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.SpaceSplittingFarSumWeighted

/-! # True fine far cross sums are bounded by the actual source distance maxima -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem spaceSplittingFarCrossSum_le_distance_maxima (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {a p : ℕ} (hap : a ≤ p)
    (X Y : Fin 2 → ℤ) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂))
    (hbound₁ : ∀ x w, |b₁ x w| ≤ 1) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    (K v : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) {Z : Set (Plane × Plane)} (hZ : MeasurableSet Z)
    (hmajor : ∀ P ∈ spaceSplittingFinePairs ρ a p X Y,
      ∀ Q ∈ spaceSplittingFinePairs ρ a p X Y, ¬spaceSplittingNear p P Q →
        ∀ x ∈ dyadicCube p P.1, ∀ x' ∈ dyadicCube p Q.1,
          ∀ y ∈ dyadicCube p P.2, ∀ y' ∈ dyadicCube p Q.2,
            ‖spaceSplittingAveragedCircleKernel b₁ b₂ K v x x' y y'‖ ≤
              δ + ((2 : ℝ) ^ (25 : ℕ) * (2 : ℝ) ^ v) *
                (spaceSplittingFarComparableSet p).indicator (fun z ↦
                  (spaceSplittingWeightedKernel ((2 : ℝ) ^ (-(v : ℝ))) Z Z z).toReal)
                  ((x, x'), (y, y'))) :
    spaceSplittingFarCrossSum ρ a p X Y b₁ b₂ K v ≤
      δ * (ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y)) ^ 2 +
        (2 : ℝ) ^ (90 : ℕ) * ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y) *
          ∑ n ∈ Finset.Ioo a (p + 12), spaceSplittingDistanceMaximum ρ a n X Y Z v := by
  exact (spaceSplittingFarCrossSum_le_weighted_kernel ρ hρ hap X Y hb₁ hb₂
    hbound₁ hbound₂ K v hδ (by positivity) hZ hmajor).trans
      (add_le_add le_rfl (spaceSplitting_far_kernel_toReal_le ρ hρ a p X Y hZ v))

end FalconerThetaGauge
