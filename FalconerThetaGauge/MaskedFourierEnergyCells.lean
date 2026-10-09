module

public import FalconerThetaGauge.MaskedFourierEnergyAverage
public import FalconerThetaGauge.RegularMeasureExcessCount

/-! # The Fourier mass bound for actual dyadic cells -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem maskedFourierEnergy_cells_le_max (ρ₁ ρ₂ : Measure Plane)
    [IsProbabilityMeasure ρ₁] [IsProbabilityMeasure ρ₂]
    (hρ₁ : ρ₁ unitSquare = 1) (hρ₂ : ρ₂ unitSquare = 1)
    (a : ℕ) (P Q : Fin 2 → ℤ) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂))
    (hbound₁ : ∀ x w, |b₁ x w| ≤ 1) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (K v : ℕ) :
    maskedFourierEnergy ρ₁ ρ₂ (dyadicCube a P) (dyadicCube a Q) b₁ b₂ K v ≤
      2600 * (4 : ℝ) ^ v * (maxCellMass ρ₁ a * maxCellMass ρ₂ a) := by
  apply (maskedFourierEnergy_le ρ₁ ρ₂ _ _ hb₁ hb₂ hbound₁ hbound₂ K v).trans
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (unitCellWeight_le_maxCellMass_all ρ₁ hρ₁ a P)
      (unitCellWeight_le_maxCellMass_all ρ₂ hρ₂ a Q) measureReal_nonneg
      (maxCellMass_nonneg ρ₁ a)) (by positivity)

/-- The second half of source (7.1), with the actual excess of the actual measure. -/
theorem maskedFourierEnergy_cells_le_excess (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {N : ℕ} (hN : 0 < N) (a : ℕ) (P Q : Fin 2 → ℤ)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (K v : ℕ) :
    maskedFourierEnergy ρ ρ (dyadicCube a P) (dyadicCube a Q) b₁ b₂ K v ≤
      2600 * (4 : ℝ) ^ ((v : ℝ) - a) *
        (2 : ℝ) ^ (-2 * N * regularMeasureExcess ρ N a) := by
  convert maskedFourierEnergy_cells_le_max ρ ρ hρ hρ a P Q hb₁ hb₂ hbound₁ hbound₂ K v using 1
  rw [maxCellMass_eq_power_excess ρ hρ hN a]
  have hfour (u : ℝ) : (4 : ℝ) ^ u = (2 : ℝ) ^ (2 * u) := by
    rw [Real.rpow_mul (by norm_num)]
    norm_num
  rw [← Real.rpow_natCast, hfour, hfour]
  simp only [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  congr 1
  ring

end FalconerThetaGauge
