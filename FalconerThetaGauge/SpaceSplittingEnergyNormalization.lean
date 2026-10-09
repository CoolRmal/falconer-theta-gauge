module

public import FalconerThetaGauge.SpaceSplittingFarSumEnergy

/-! # The actual cell mass normalization in source Estimate 7.8 -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

def spaceSplittingFineEnergyAverage (ρ : Measure Plane) (a p : ℕ) (X Y : Fin 2 → ℤ)
    (b₁ b₂ : Plane → UnitCircle → ℝ) (K v : ℕ) : ℝ :=
  ∑ P ∈ spaceSplittingFinePairs ρ a p X Y,
    (ρ.real (dyadicCube p P.1) * ρ.real (dyadicCube p P.2) /
      (ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y))) *
        maskedFourierEnergy ρ ρ (dyadicCube p P.1) (dyadicCube p P.2) b₁ b₂ K v

theorem spaceSplittingFineEnergyAverage_nonneg (ρ : Measure Plane) (a p : ℕ)
    (X Y : Fin 2 → ℤ) (b₁ b₂ : Plane → UnitCircle → ℝ) (K v : ℕ) :
    0 ≤ spaceSplittingFineEnergyAverage ρ a p X Y b₁ b₂ K v := by
  apply sum_nonneg
  intro P _
  exact mul_nonneg (div_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg)
    (mul_nonneg measureReal_nonneg measureReal_nonneg))
      (maskedFourierEnergy_nonneg ρ ρ _ _ b₁ b₂ K v)

theorem mass_mul_spaceSplittingFineEnergyAverage (ρ : Measure Plane) (a p : ℕ)
    (X Y : Fin 2 → ℤ) (b₁ b₂ : Plane → UnitCircle → ℝ) (K v : ℕ)
    (hm : 0 < ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y)) :
    (ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y)) *
        spaceSplittingFineEnergyAverage ρ a p X Y b₁ b₂ K v =
      ∑ P ∈ spaceSplittingFinePairs ρ a p X Y,
        (ρ.real (dyadicCube p P.1) * ρ.real (dyadicCube p P.2)) *
          maskedFourierEnergy ρ ρ (dyadicCube p P.1) (dyadicCube p P.2) b₁ b₂ K v := by
  unfold spaceSplittingFineEnergyAverage
  rw [mul_sum]
  apply sum_congr rfl
  intro P _
  obtain ⟨hmX, hmY⟩ := mul_ne_zero_iff.1 hm.ne'
  field_simp [hmX, hmY]

/-- Schur's exact near term divided by the genuine positive root carrier mass. -/
theorem maskedFourierEnergy_le_normalized_near_and_far (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {a p : ℕ} (hap : a ≤ p)
    (X Y : Fin 2 → ℤ) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂))
    (hbound₁ : ∀ x w, |b₁ x w| ≤ 1) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    (K v : ℕ) (hm : 0 < ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y)) :
    maskedFourierEnergy ρ ρ (dyadicCube a X) (dyadicCube a Y) b₁ b₂ K v ≤
      (81 : ℝ) ^ 2 * spaceSplittingFineEnergyAverage ρ a p X Y b₁ b₂ K v +
        spaceSplittingFarCrossSum ρ a p X Y b₁ b₂ K v /
          (ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y)) := by
  apply (le_of_mul_le_mul_left _ hm)
  have h := mass_mul_maskedFourierEnergy_le_near_schur ρ ρ hρ hρ hap X Y
    hb₁ hb₂ hbound₁ hbound₂ K v
  have he := mass_mul_spaceSplittingFineEnergyAverage ρ a p X Y b₁ b₂ K v hm
  change _ ≤ (81 : ℝ) ^ 2 * _ + spaceSplittingFarCrossSum ρ a p X Y b₁ b₂ K v at h
  convert h using 1
  rw [mul_add, ← mul_assoc, mul_comm
    (ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y)) ((81 : ℝ) ^ 2),
    mul_assoc, he, mul_div_cancel₀ _ hm.ne']
  rfl

end FalconerThetaGauge
