module

public import FalconerThetaGauge.SpaceSplittingDistanceCover

/-! # The actual far weighted kernel is controlled by the source depth energies -/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem lintegral_spaceSplittingWeightedKernel_ne_top (ρ : Measure Plane)
    [IsFiniteMeasure ρ] {n : ℕ} {P P' Q Q' : Fin 2 → ℤ}
    (hsepX : SeparatedDyadicCells n P P') (hsepY : SeparatedDyadicCells n Q Q')
    {Z₁ Z₂ : Set (Plane × Plane)} (hZ₁ : MeasurableSet Z₁) (hZ₂ : MeasurableSet Z₂)
    (v : ℕ) :
    (∫⁻ z, spaceSplittingWeightedKernel ((2 : ℝ) ^ (-(v : ℝ))) Z₁ Z₂ z
      ∂((ρ.restrict (dyadicCube n P)).prod (ρ.restrict (dyadicCube n P'))).prod
        ((ρ.restrict (dyadicCube n Q)).prod (ρ.restrict (dyadicCube n Q')))) ≠ ⊤ := by
  have := isFiniteMeasure_passingWeightedDistanceMeasure_of_separatedCells ρ ρ hsepX Z₁
  have := isFiniteMeasure_passingWeightedDistanceMeasure_of_separatedCells ρ ρ hsepY Z₂
  rw [lintegral_spaceSplittingWeightedKernel_eq ρ ρ ρ ρ _ _ _ _ hZ₁ hZ₂]
  exact lintegral_scalarBinningKernel_ne_top _ _ (by positivity)

def spaceSplittingDepthKernelSum (ρ : Measure Plane) (a n : ℕ) (X Y : Fin 2 → ℤ)
    (Z : Set (Plane × Plane)) (v : ℕ) : ℝ≥0∞ :=
  ∑ P ∈ spaceSplittingSeparatedPairs ρ a n X,
    ∑ Q ∈ spaceSplittingSeparatedPairs ρ a n Y,
      ∫⁻ z, spaceSplittingWeightedKernel ((2 : ℝ) ^ (-(v : ℝ))) Z Z z
        ∂((ρ.restrict (dyadicCube n P.1)).prod (ρ.restrict (dyadicCube n P.2))).prod
          ((ρ.restrict (dyadicCube n Q.1)).prod (ρ.restrict (dyadicCube n Q.2)))

theorem spaceSplittingDepthKernelSum_ne_top (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (a n : ℕ) (X Y : Fin 2 → ℤ) {Z : Set (Plane × Plane)}
    (hZ : MeasurableSet Z) (v : ℕ) : spaceSplittingDepthKernelSum ρ a n X Y Z v ≠ ⊤ := by
  apply ENNReal.sum_ne_top.2
  intro P hP
  apply ENNReal.sum_ne_top.2
  intro Q hQ
  exact lintegral_spaceSplittingWeightedKernel_ne_top ρ
    (mem_filter.1 hP).2 (mem_filter.1 hQ).2 hZ hZ v

theorem spaceSplittingDepthKernelSum_toReal_le (ρ : Measure Plane) [IsFiniteMeasure ρ]
    {a n : ℕ} (han : a ≤ n) (X Y : Fin 2 → ℤ) {Z : Set (Plane × Plane)}
    (hZ : MeasurableSet Z) (v : ℕ) :
    (2 : ℝ) ^ (25 : ℕ) * (2 : ℝ) ^ v *
        (spaceSplittingDepthKernelSum ρ a n X Y Z v).toReal ≤
      (2 : ℝ) ^ (90 : ℕ) * spaceSplittingDistanceMaximum ρ a n X Y Z v *
        ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y) := by
  have hpq (P : (Fin 2 → ℤ) × (Fin 2 → ℤ))
      (hP : P ∈ spaceSplittingSeparatedPairs ρ a n X)
      (Q : (Fin 2 → ℤ) × (Fin 2 → ℤ)) (hQ : Q ∈ spaceSplittingSeparatedPairs ρ a n Y) :=
    lintegral_spaceSplittingWeightedKernel_ne_top ρ
      (mem_filter.1 hP).2 (mem_filter.1 hQ).2 hZ hZ v
  unfold spaceSplittingDepthKernelSum
  rw [ENNReal.toReal_sum (fun P hP ↦ ENNReal.sum_ne_top.2 (fun Q hQ ↦ hpq P hP Q hQ))]
  have heq (P : (Fin 2 → ℤ) × (Fin 2 → ℤ))
      (hP : P ∈ spaceSplittingSeparatedPairs ρ a n X) :=
    ENNReal.toReal_sum (fun Q hQ ↦ hpq P hP Q hQ)
  calc
    _ = (2 : ℝ) ^ (25 : ℕ) *
        (∑ P ∈ spaceSplittingSeparatedPairs ρ a n X,
          ∑ Q ∈ spaceSplittingSeparatedPairs ρ a n Y,
            (2 : ℝ) ^ v * (∫⁻ z,
              spaceSplittingWeightedKernel ((2 : ℝ) ^ (-(v : ℝ))) Z Z z
                ∂((ρ.restrict (dyadicCube n P.1)).prod
                  (ρ.restrict (dyadicCube n P.2))).prod
                    ((ρ.restrict (dyadicCube n Q.1)).prod
                      (ρ.restrict (dyadicCube n Q.2)))).toReal) := by
      rw [mul_assoc, mul_sum]
      congr 1
      apply sum_congr rfl
      intro P hP
      rw [heq P hP, mul_sum]
    _ ≤ _ := spaceSplitting_regrouped_kernel_le ρ han X Y hZ v

/-- The integrated Case B kernel has precisely the true depth maxima and the source constant. -/
theorem spaceSplitting_far_kernel_toReal_le (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) (a p : ℕ) (X Y : Fin 2 → ℤ)
    {Z : Set (Plane × Plane)} (hZ : MeasurableSet Z) (v : ℕ) :
    (2 : ℝ) ^ (25 : ℕ) * (2 : ℝ) ^ v *
      (∫⁻ z, spaceSplittingWeightedKernel ((2 : ℝ) ^ (-(v : ℝ))) Z Z z
        ∂(spaceSplittingRootFourMeasure ρ a X Y).restrict
          (spaceSplittingFarComparableSet p)).toReal ≤
      (2 : ℝ) ^ (90 : ℕ) * ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y) *
        ∑ n ∈ Finset.Ioo a (p + 12), spaceSplittingDistanceMaximum ρ a n X Y Z v := by
  have h := lintegral_spaceSplittingFarComparable_le_depth_sum ρ hρ a p X Y
    (spaceSplittingWeightedKernel ((2 : ℝ) ^ (-(v : ℝ))) Z Z)
  change _ ≤ ∑ n ∈ Finset.Ioo a (p + 12), spaceSplittingDepthKernelSum ρ a n X Y Z v at h
  have hfin := fun n (_hn : n ∈ Finset.Ioo a (p + 12)) ↦
    spaceSplittingDepthKernelSum_ne_top ρ a n X Y hZ v
  have ht := ENNReal.toReal_mono (ENNReal.sum_ne_top.2 hfin) h
  rw [ENNReal.toReal_sum hfin] at ht
  calc
    _ ≤ (2 : ℝ) ^ (25 : ℕ) * (2 : ℝ) ^ v *
        ∑ n ∈ Finset.Ioo a (p + 12), (spaceSplittingDepthKernelSum ρ a n X Y Z v).toReal :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = ∑ n ∈ Finset.Ioo a (p + 12),
        (2 : ℝ) ^ (25 : ℕ) * (2 : ℝ) ^ v *
          (spaceSplittingDepthKernelSum ρ a n X Y Z v).toReal := by rw [mul_sum]
    _ ≤ ∑ n ∈ Finset.Ioo a (p + 12),
        (2 : ℝ) ^ (90 : ℕ) * spaceSplittingDistanceMaximum ρ a n X Y Z v *
          ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y) := by
      apply sum_le_sum
      intro n hn
      exact spaceSplittingDepthKernelSum_toReal_le ρ (mem_Ioo.1 hn).1.le X Y hZ v
    _ = _ := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro n _
      ring

end FalconerThetaGauge
