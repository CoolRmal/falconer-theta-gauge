module

public import FalconerThetaGauge.SpaceSplittingKernelEnergy
public import FalconerThetaGauge.ScheduledStateEnergies

/-! # The actual separated-cell weighted kernel sums obey the source `2⁹⁰` bound -/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

def spaceSplittingDistanceMaximum (ρ : Measure Plane) (a n : ℕ) (X Y : Fin 2 → ℤ)
    (Z : Set (Plane × Plane)) (v : ℕ) : ℝ :=
  finiteEnergyMaximum
    (spaceSplittingSeparatedPairs ρ a n X ∪ spaceSplittingSeparatedPairs ρ a n Y) fun P ↦
      maskedDistanceEnergy ρ ρ (dyadicCube n P.1) (dyadicCube n P.2) Z v

theorem real_mass_pair_pos_of_mem_spaceSplittingSeparatedPairs (ρ : Measure Plane)
    {a n : ℕ} {X : Fin 2 → ℤ} {P : (Fin 2 → ℤ) × (Fin 2 → ℤ)}
    (hP : P ∈ spaceSplittingSeparatedPairs ρ a n X) :
    0 < ρ.real (dyadicCube n P.1) * ρ.real (dyadicCube n P.2) := by
  obtain ⟨hP, _⟩ := mem_filter.1 hP
  obtain ⟨hP₁, hP₂⟩ := mem_product.1 hP
  exact mul_pos (mem_filter.1 hP₁).2.2 (mem_filter.1 hP₂).2.2

/-- The literal depth contribution of the weighted collision kernel costs at most `2⁹⁰`. -/
theorem spaceSplitting_regrouped_kernel_le (ρ : Measure Plane) [IsFiniteMeasure ρ]
    {a n : ℕ} (han : a ≤ n) (X Y : Fin 2 → ℤ) {Z : Set (Plane × Plane)}
    (hZ : MeasurableSet Z) (v : ℕ) :
    (2 : ℝ) ^ (25 : ℕ) *
      (∑ P ∈ spaceSplittingSeparatedPairs ρ a n X,
        ∑ Q ∈ spaceSplittingSeparatedPairs ρ a n Y,
          (2 : ℝ) ^ v * (∫⁻ p,
            spaceSplittingWeightedKernel ((2 : ℝ) ^ (-(v : ℝ))) Z Z p
              ∂((ρ.restrict (dyadicCube n P.1)).prod (ρ.restrict (dyadicCube n P.2))).prod
                ((ρ.restrict (dyadicCube n Q.1)).prod
                  (ρ.restrict (dyadicCube n Q.2)))).toReal) ≤
      (2 : ℝ) ^ (90 : ℕ) * spaceSplittingDistanceMaximum ρ a n X Y Z v *
        ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y) := by
  let D := spaceSplittingDistanceMaximum ρ a n X Y Z v
  let m := fun P : (Fin 2 → ℤ) × (Fin 2 → ℤ) ↦
    ρ.real (dyadicCube n P.1) * ρ.real (dyadicCube n P.2)
  have hD : 0 ≤ D := finiteEnergyMaximum_nonneg _ _
  have hcell (P : (Fin 2 → ℤ) × (Fin 2 → ℤ))
      (hP : P ∈ spaceSplittingSeparatedPairs ρ a n X)
      (Q : (Fin 2 → ℤ) × (Fin 2 → ℤ))
      (hQ : Q ∈ spaceSplittingSeparatedPairs ρ a n Y) :
      (2 : ℝ) ^ v * (∫⁻ p,
        spaceSplittingWeightedKernel ((2 : ℝ) ^ (-(v : ℝ))) Z Z p
          ∂((ρ.restrict (dyadicCube n P.1)).prod (ρ.restrict (dyadicCube n P.2))).prod
            ((ρ.restrict (dyadicCube n Q.1)).prod (ρ.restrict (dyadicCube n Q.2)))).toReal ≤
      10 * D * Real.sqrt (m P) * Real.sqrt (m Q) := by
    have hp := spaceSplittingWeightedKernel_toReal_le_energy ρ
      (mem_filter.1 hP).2 (mem_filter.1 hQ).2
      (real_mass_pair_pos_of_mem_spaceSplittingSeparatedPairs ρ hP)
      (real_mass_pair_pos_of_mem_spaceSplittingSeparatedPairs ρ hQ) hZ hZ v
    have hPmax : maskedDistanceEnergy ρ ρ (dyadicCube n P.1) (dyadicCube n P.2) Z v ≤ D := by
      dsimp only [D, spaceSplittingDistanceMaximum]
      exact le_finiteEnergyMaximum
        (spaceSplittingSeparatedPairs ρ a n X ∪ spaceSplittingSeparatedPairs ρ a n Y)
        (fun R ↦ maskedDistanceEnergy ρ ρ (dyadicCube n R.1) (dyadicCube n R.2) Z v)
        (mem_union_left _ hP)
    have hQmax : maskedDistanceEnergy ρ ρ (dyadicCube n Q.1) (dyadicCube n Q.2) Z v ≤ D := by
      dsimp only [D, spaceSplittingDistanceMaximum]
      exact le_finiteEnergyMaximum
        (spaceSplittingSeparatedPairs ρ a n X ∪ spaceSplittingSeparatedPairs ρ a n Y)
        (fun R ↦ maskedDistanceEnergy ρ ρ (dyadicCube n R.1) (dyadicCube n R.2) Z v)
        (mem_union_right _ hQ)
    have h := sqrt_mass_energy_product_le (m := m P) (n := m Q)
      (mul_nonneg measureReal_nonneg measureReal_nonneg)
      (mul_nonneg measureReal_nonneg measureReal_nonneg)
      (maskedDistanceEnergy_nonneg ρ ρ _ _ Z v) hD hPmax hQmax
    apply hp.trans
    convert mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 10) using 1
    ring
  have hx := sum_sqrt_mass_spaceSplittingSeparatedPairs_le ρ han X
  have hy := sum_sqrt_mass_spaceSplittingSeparatedPairs_le ρ han Y
  have hsum :
      (∑ P ∈ spaceSplittingSeparatedPairs ρ a n X,
        ∑ Q ∈ spaceSplittingSeparatedPairs ρ a n Y,
          (2 : ℝ) ^ v * (∫⁻ p,
            spaceSplittingWeightedKernel ((2 : ℝ) ^ (-(v : ℝ))) Z Z p
              ∂((ρ.restrict (dyadicCube n P.1)).prod (ρ.restrict (dyadicCube n P.2))).prod
                ((ρ.restrict (dyadicCube n Q.1)).prod
                  (ρ.restrict (dyadicCube n Q.2)))).toReal) ≤
      10 * D * ((20001 : ℝ) ^ 2 * ρ.real (dyadicCube a X)) *
        ((20001 : ℝ) ^ 2 * ρ.real (dyadicCube a Y)) := by
    calc
      _ ≤ ∑ P ∈ spaceSplittingSeparatedPairs ρ a n X,
          ∑ Q ∈ spaceSplittingSeparatedPairs ρ a n Y,
            10 * D * Real.sqrt (m P) * Real.sqrt (m Q) :=
        sum_le_sum fun P hP ↦ sum_le_sum fun Q hQ ↦ hcell P hP Q hQ
      _ = (10 * D) * (∑ P ∈ spaceSplittingSeparatedPairs ρ a n X, Real.sqrt (m P)) *
          (∑ Q ∈ spaceSplittingSeparatedPairs ρ a n Y, Real.sqrt (m Q)) := by
        simp_rw [← mul_sum, ← sum_mul]
        rw [← mul_sum]
      _ ≤ _ := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hx (by positivity)) hy
          (sum_nonneg (by intros; positivity)) (by positivity)
  calc
    _ ≤ (2 : ℝ) ^ (25 : ℕ) *
        (10 * D * ((20001 : ℝ) ^ 2 * ρ.real (dyadicCube a X)) *
          ((20001 : ℝ) ^ 2 * ρ.real (dyadicCube a Y))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = spaceSplittingRegroupingConstant *
        (D * ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y)) := by
      unfold spaceSplittingRegroupingConstant
      ring
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_right spaceSplittingRegroupingConstant_le_source
        (by positivity : 0 ≤ D * ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y)) using 1
      ring

end FalconerThetaGauge
