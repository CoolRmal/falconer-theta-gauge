/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.ScheduledStateEnergiesOrthogonality
public import FalconerThetaGauge.RegularFilteredMeasureMixtureRoot

/-! # Exact entry-cell passage for the actual root piece symbol class -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem dyadicCube_zero_eq_unitSquare : dyadicCube 0 (0 : Fin 2 → ℤ) = unitSquare := by
  ext x
  simp only [dyadicCube, unitSquare, mem_ofPred_eq, pow_zero, one_mul, Pi.zero_apply,
    Int.cast_zero, zero_add, Set.mem_Ico]

theorem zero_mem_occupiedUnitCells (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) : (0 : Fin 2 → ℤ) ∈ occupiedUnitCells ρ 0 := by
  apply mem_filter.mpr
  constructor
  · apply (mem_unitCellIndices_iff 0 _).mpr
    intro i
    norm_num
  · simp only [unitCellWeight, dyadicCube_zero_eq_unitSquare, Measure.real, hρ,
      ENNReal.toReal_one]
    norm_num

theorem regularMeasurePieceTests_filter_entry (ρ : Measure Plane) {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) :
    (regularMeasurePieceTests ρ θ N).filter
      (fun test ↦ regularMeasureEntryDepth ρ θ N < test.anchor) =
      profileRemainingTests (regularMeasureExcess ρ N) (blockCount θ N) N
        (regularMeasureEntryDepth ρ θ N) N (regularMeasureEntryDepth ρ θ N) := by
  have hN : 0 < N := by have := hpar.1; omega
  rw [regularMeasurePieceTests, profilePieceTests_filter_after_entry _ (blockCount_pos θ hN),
    profileRemainingTests_at_base _ (blockCount_pos θ hN) (le_refl N)]

theorem scheduledFourierEnergySup_piece_le_entry_state (ρ : Measure Plane)
    [IsFiniteMeasure ρ] {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) (i : ℕ)
    {P Q : Fin 2 → ℤ}
    (hP : P ∈ occupiedUnitCells ρ (regularMeasureEntryDepth ρ θ N))
    (hQ : Q ∈ occupiedUnitCells ρ (regularMeasureEntryDepth ρ θ N)) :
    scheduledFourierEnergySup ρ ρ
        (dyadicCube (regularMeasureEntryDepth ρ θ N) P)
        (dyadicCube (regularMeasureEntryDepth ρ θ N) Q) (tolerance θ N * N)
        (directionalLevelWidth (maskLevelCount θ N) i) (8 * expansionCount θ N)
        (regularMeasurePieceTests ρ θ N) (regularMeasurePieceTests ρ θ N)
        (2 * expansionCount θ N) (8 * expansionCount θ N) N ≤
      regularMeasureStateEnergy ρ θ N i
        (.fourier (regularMeasureEntryDepth ρ θ N) N (regularMeasureEntryDepth ρ θ N) N) := by
  apply (scheduledFourierEnergySup_drop_reached ρ ρ _ _ _ _ _ (by omega)
    (regularMeasureEntryDepth ρ θ N) hP hQ (8 * expansionCount θ N) N).trans
  rw [regularMeasurePieceTests_filter_entry ρ hpar]
  change _ ≤ profileFourierStateEnergy ρ _ _ _ _ _ _ _ _ _ _ _ _ _
  unfold profileFourierStateEnergy
  exact le_finiteEnergyMaximum (profileOccupiedCellPairs ρ (regularMeasureEntryDepth ρ θ N))
    (fun R ↦ scheduledFourierEnergySup ρ ρ
      (dyadicCube (regularMeasureEntryDepth ρ θ N) R.1)
      (dyadicCube (regularMeasureEntryDepth ρ θ N) R.2) (tolerance θ N * N)
      (directionalLevelWidth (maskLevelCount θ N) i) (8 * expansionCount θ N)
      (profileRemainingTests (regularMeasureExcess ρ N) (blockCount θ N) N
        (regularMeasureEntryDepth ρ θ N) N (regularMeasureEntryDepth ρ θ N))
      (profileRemainingTests (regularMeasureExcess ρ N) (blockCount θ N) N
        (regularMeasureEntryDepth ρ θ N) N (regularMeasureEntryDepth ρ θ N))
      (2 * expansionCount θ N) (8 * expansionCount θ N) N)
    (j := (P, Q)) (Finset.mem_product.mpr ⟨hP, hQ⟩)

theorem sum_maskedFourierEnergy_piece_le_entry_state (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) (i : ℕ)
    {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ (tolerance θ N * N)
      (directionalLevelWidth (maskLevelCount θ N) i) (8 * expansionCount θ N)
      (regularMeasurePieceTests ρ θ N) (2 * expansionCount θ N))
    (hb₂ : b₂ ∈ scheduledSymbolClass ρ (tolerance θ N * N)
      (directionalLevelWidth (maskLevelCount θ N) i) (8 * expansionCount θ N)
      (regularMeasurePieceTests ρ θ N) (2 * expansionCount θ N)) :
    let c := regularMeasureEntryDepth ρ θ N
    (∑ P ∈ (occupiedCellDescendants ρ 0 c 0).product (occupiedCellDescendants ρ 0 c 0),
      (ρ.real (dyadicCube c P.1) * ρ.real (dyadicCube c P.2)) /
        (ρ.real (dyadicCube 0 0) * ρ.real (dyadicCube 0 0)) *
        maskedFourierEnergy ρ ρ (dyadicCube c P.1) (dyadicCube c P.2) b₁ b₂
          (8 * expansionCount θ N) N) ≤
      regularMeasureStateEnergy ρ θ N i (.fourier c N c N) := by
  let c := regularMeasureEntryDepth ρ θ N
  let F := regularMeasureStateEnergy ρ θ N i (.fourier c N c N)
  have hF : 0 ≤ F := regularMeasureStateEnergy_nonneg ρ θ N i (.fourier c N c N)
  calc
    _ ≤ ∑ P ∈ (occupiedCellDescendants ρ 0 c 0).product (occupiedCellDescendants ρ 0 c 0),
        (ρ.real (dyadicCube c P.1) * ρ.real (dyadicCube c P.2)) /
          (ρ.real (dyadicCube 0 0) * ρ.real (dyadicCube 0 0)) * F := by
      apply Finset.sum_le_sum
      intro P hP
      obtain ⟨hP, hQ⟩ := Finset.mem_product.mp hP
      have h₁ := maskedFourierEnergy_le_scheduledFourierEnergySup ρ ρ
        (dyadicCube c P.1) (dyadicCube c P.2) _ _ _ _ _ (by omega)
        (8 * expansionCount θ N) N hb₁ hb₂
      have h₂ := scheduledFourierEnergySup_piece_le_entry_state ρ hpar i
        (occupiedCellDescendant_mem_occupied ρ hP) (occupiedCellDescendant_mem_occupied ρ hQ)
      exact mul_le_mul_of_nonneg_left (h₁.trans h₂) (by positivity)
    _ = (∑ P ∈
        (occupiedCellDescendants ρ 0 c 0).product (occupiedCellDescendants ρ 0 c 0),
        (ρ.real (dyadicCube c P.1) * ρ.real (dyadicCube c P.2)) /
          (ρ.real (dyadicCube 0 0) * ρ.real (dyadicCube 0 0))) * F := by rw [sum_mul]
    _ ≤ 1 * F := mul_le_mul_of_nonneg_right
      (sum_occupiedCellPairs_normalized_mass_le_one ρ (Nat.zero_le c)
        (zero_mem_occupiedUnitCells ρ hρ) (zero_mem_occupiedUnitCells ρ hρ)) hF
    _ = F := one_mul F

end FalconerThetaGauge
