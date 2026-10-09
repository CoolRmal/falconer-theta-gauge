module

public import FalconerThetaGauge.MaskedFourierArcPair
public import FalconerThetaGauge.OrthogonalitySymbolLinks

/-! # The literal arc amplitudes split over their genuinely active occupied descendants -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman

theorem maskedFourierAmplitude_eq_zero_of_inactive (ρ : Measure Plane)
    (a p : ℕ) (X P : Fin 2 → ℤ) (K : ℕ) (ℓ : ℝ)
    (arc : Fin (angularPartitionCount ℓ)) (b : Plane → UnitCircle → ℝ)
    (hP : P ∈ occupiedCellDescendants ρ a p X)
    (hnot : P ∉ symbolActiveCellDescendants ρ a p X K ℓ arc b)
    (r : ℝ) (w : UnitCircle) (hχ : equalArcCutoff K ℓ arc w ≠ 0) :
    maskedFourierAmplitude ρ (dyadicCube p P) b r w = 0 := by
  unfold maskedFourierAmplitude
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro x hx
  have hb : b x w = 0 := by
    by_contra hb
    exact hnot (mem_filter.mpr ⟨hP, x, hx, w, hχ, hb⟩)
  simp only [hb, Complex.ofReal_zero, mul_zero]

theorem sqrt_cutoff_mul_maskedFourierAmplitude_active (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ GaugeSeparatedMeasures.unitSquare = 1)
    {a p : ℕ} (hap : a ≤ p) (X : Fin 2 → ℤ)
    {b : Plane → UnitCircle → ℝ} (hb : Measurable (uncurry b))
    (hbound : ∀ x w, |b x w| ≤ 1) (K : ℕ) (ℓ : ℝ)
    (arc : Fin (angularPartitionCount ℓ)) (r : ℝ) (w : UnitCircle) :
    (Real.sqrt (equalArcCutoff K ℓ arc w) : ℂ) *
        maskedFourierAmplitude ρ (dyadicCube a X) b r w =
      ∑ P ∈ symbolActiveCellDescendants ρ a p X K ℓ arc b,
        (Real.sqrt (equalArcCutoff K ℓ arc w) : ℂ) *
          maskedFourierAmplitude ρ (dyadicCube p P) b r w := by
  rw [maskedFourierAmplitude_occupiedCellDescendants ρ hρ hap X hb hbound, mul_sum]
  symm
  apply sum_subset (filter_subset _ _)
  intro P hP hnot
  by_cases hχ : equalArcCutoff K ℓ arc w = 0
  · simp only [hχ, Real.sqrt_zero, Complex.ofReal_zero, zero_mul]
  · rw [maskedFourierAmplitude_eq_zero_of_inactive ρ a p X P K ℓ arc b
      hP hnot r w hχ, mul_zero]

/-- The actual parent amplitude is the sum over precisely the source's active fine cell pairs. -/
theorem maskedFourierArcPairAmplitude_active (ρ₁ ρ₂ : Measure Plane)
    [IsProbabilityMeasure ρ₁] [IsProbabilityMeasure ρ₂]
    (hρ₁ : ρ₁ GaugeSeparatedMeasures.unitSquare = 1)
    (hρ₂ : ρ₂ GaugeSeparatedMeasures.unitSquare = 1)
    {a p : ℕ} (hap : a ≤ p) (X Y : Fin 2 → ℤ)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (K : ℕ) (ℓ : ℝ)
    (i j : Fin (angularPartitionCount ℓ)) (z : ℝ × UnitCircle × UnitCircle) :
    maskedFourierArcPairAmplitude ρ₁ ρ₂ (dyadicCube a X) (dyadicCube a Y)
        b₁ b₂ K ℓ i j z =
      ∑ P ∈ (symbolActiveCellDescendants ρ₁ a p X K ℓ i b₁).product
          (symbolActiveCellDescendants ρ₂ a p Y K ℓ j b₂),
        maskedFourierArcPairAmplitude ρ₁ ρ₂ (dyadicCube p P.1) (dyadicCube p P.2)
          b₁ b₂ K ℓ i j z := by
  have he : ∀ A B,
      maskedFourierArcPairAmplitude ρ₁ ρ₂ A B b₁ b₂ K ℓ i j z =
        ((Real.sqrt (equalArcCutoff K ℓ i z.2.1) : ℂ) *
          maskedFourierAmplitude ρ₁ A b₁ z.1 z.2.1) *
        ((Real.sqrt (equalArcCutoff K ℓ j z.2.2) : ℂ) *
          maskedFourierAmplitude ρ₂ B b₂ z.1 z.2.2) := by
    intro A B
    simp only [maskedFourierArcPairAmplitude, Complex.ofReal_mul]
    ring
  simp_rw [he]
  rw [sqrt_cutoff_mul_maskedFourierAmplitude_active ρ₁ hρ₁ hap X hb₁ hbound₁,
    sqrt_cutoff_mul_maskedFourierAmplitude_active ρ₂ hρ₂ hap Y hb₂ hbound₂,
    sum_mul]
  simp_rw [mul_sum]
  exact (sum_product
    (symbolActiveCellDescendants ρ₁ a p X K ℓ i b₁)
    (symbolActiveCellDescendants ρ₂ a p Y K ℓ j b₂)
    (fun P ↦ ((Real.sqrt (equalArcCutoff K ℓ i z.2.1) : ℂ) *
      maskedFourierAmplitude ρ₁ (dyadicCube p P.1) b₁ z.1 z.2.1) *
      ((Real.sqrt (equalArcCutoff K ℓ j z.2.2) : ℂ) *
        maskedFourierAmplitude ρ₂ (dyadicCube p P.2) b₂ z.1 z.2.2))).symm

end FalconerThetaGauge
