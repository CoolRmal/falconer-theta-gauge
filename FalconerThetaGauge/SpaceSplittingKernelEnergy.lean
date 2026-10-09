module

public import FalconerThetaGauge.SpaceSplittingWeightedKernel
public import FalconerThetaGauge.SpaceSplittingSeparatedPartners

/-! # The actual weighted space-splitting kernel is controlled by the actual source energies -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem isFiniteMeasure_passingWeightedDistanceMeasure_of_separatedCells
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    {n : ℕ} {P P' : Fin 2 → ℤ} (hsep : SeparatedDyadicCells n P P')
    (Z : Set (Plane × Plane)) :
    IsFiniteMeasure (passingWeightedDistanceMeasure ρ₁ ρ₂
      (dyadicCube n P) (dyadicCube n P') Z) :=
  isFiniteMeasure_passingWeightedDistanceMeasure ρ₁ ρ₂
    (measurableSet_dyadicCube n P) (measurableSet_dyadicCube n P') Z
    (fun _x hx _y hy ↦ crossDistanceWeight_le_of_dist
      (mul_pos (by norm_num : (0 : ℝ) < 500) (dyadicRadius_pos n))
      (dist_bounds_of_separatedDyadicCells hsep hx hy).1)

/-- The actual four-point weighted integral, with the true distance energies on both sides. -/
theorem spaceSplittingWeightedKernel_toReal_le_energy (ρ : Measure Plane) [IsFiniteMeasure ρ]
    {n : ℕ} {P P' Q Q' : Fin 2 → ℤ} (hxsep : SeparatedDyadicCells n P P')
    (hysep : SeparatedDyadicCells n Q Q')
    (hxmass : 0 < ρ.real (dyadicCube n P) * ρ.real (dyadicCube n P'))
    (hymass : 0 < ρ.real (dyadicCube n Q) * ρ.real (dyadicCube n Q'))
    {Z₁ Z₂ : Set (Plane × Plane)} (hZ₁ : MeasurableSet Z₁) (hZ₂ : MeasurableSet Z₂)
    (v : ℕ) :
    (2 : ℝ) ^ v * (∫⁻ p, spaceSplittingWeightedKernel ((2 : ℝ) ^ (-(v : ℝ))) Z₁ Z₂ p
      ∂((ρ.restrict (dyadicCube n P)).prod (ρ.restrict (dyadicCube n P'))).prod
        ((ρ.restrict (dyadicCube n Q)).prod (ρ.restrict (dyadicCube n Q')))).toReal ≤
      10 * Real.sqrt
        (((ρ.real (dyadicCube n P) * ρ.real (dyadicCube n P')) *
            maskedDistanceEnergy ρ ρ (dyadicCube n P) (dyadicCube n P') Z₁ v) *
          ((ρ.real (dyadicCube n Q) * ρ.real (dyadicCube n Q')) *
            maskedDistanceEnergy ρ ρ (dyadicCube n Q) (dyadicCube n Q') Z₂ v)) := by
  let η := passingWeightedDistanceMeasure ρ ρ (dyadicCube n P) (dyadicCube n P') Z₁
  let ζ := passingWeightedDistanceMeasure ρ ρ (dyadicCube n Q) (dyadicCube n Q') Z₂
  let : IsFiniteMeasure η := isFiniteMeasure_passingWeightedDistanceMeasure_of_separatedCells
    ρ ρ hxsep Z₁
  let : IsFiniteMeasure ζ := isFiniteMeasure_passingWeightedDistanceMeasure_of_separatedCells
    ρ ρ hysep Z₂
  rw [lintegral_spaceSplittingWeightedKernel_eq ρ ρ ρ ρ _ _ _ _ hZ₁ hZ₂]
  convert dyadic_scalar_kernel_toReal_le_normalized η ζ hxmass hymass v using 1
  simp only [normalizedDistanceCollisionEnergy, maskedDistanceEnergy, Real.rpow_natCast, η, ζ]

theorem sqrt_mass_energy_product_le {m n D E B : ℝ}
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hDB : D ≤ B) (hEB : E ≤ B) :
    Real.sqrt ((m * D) * (n * E)) ≤ B * Real.sqrt m * Real.sqrt n := by
  calc
    _ ≤ Real.sqrt (B ^ 2 * (m * n)) := by
      apply Real.sqrt_le_sqrt
      have h := mul_le_mul_of_nonneg_left (mul_le_mul hDB hEB hE hB) (mul_nonneg hm hn)
      convert h using 1 <;> ring
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB, Real.sqrt_mul hm]; ring

end FalconerThetaGauge
