module

public import FalconerThetaGauge.ScheduledSymbolEnergyCells
public import FalconerThetaGauge.RegularMeasureEntryChainStates

/-! # Definition 8.4 as genuine maxima of the actual scheduled distance and Fourier energies -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- A finite energy maximum, with value zero when no cell pairs are available. -/
def finiteEnergyMaximum {ι : Type*} (I : Finset ι) (f : ι → ℝ) : ℝ :=
  sSup (insert 0 (f '' (I : Set ι)))

theorem finiteEnergyMaximum_bddAbove {ι : Type*} (I : Finset ι) (f : ι → ℝ) :
    BddAbove (insert 0 (f '' (I : Set ι))) :=
  ((I.finite_toSet.image f).insert 0).bddAbove

theorem finiteEnergyMaximum_nonneg {ι : Type*} (I : Finset ι) (f : ι → ℝ) :
    0 ≤ finiteEnergyMaximum I f :=
  le_csSup (finiteEnergyMaximum_bddAbove I f) (mem_insert 0 _)

theorem le_finiteEnergyMaximum {ι : Type*} (I : Finset ι) (f : ι → ℝ)
    {j : ι} (hj : j ∈ I) : f j ≤ finiteEnergyMaximum I f :=
  le_csSup (finiteEnergyMaximum_bddAbove I f) (mem_insert_of_mem 0 ⟨j, hj, rfl⟩)

theorem finiteEnergyMaximum_le {ι : Type*} (I : Finset ι) (f : ι → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ j ∈ I, f j ≤ B) : finiteEnergyMaximum I f ≤ B := by
  apply csSup_le (insert_nonempty 0 _)
  rintro z (rfl | ⟨j, hj, rfl⟩)
  · exact hB
  · exact hbound j hj

theorem finiteEnergyMaximum_mono {ι : Type*} (I : Finset ι) {f g : ι → ℝ}
    (h : ∀ j ∈ I, f j ≤ g j) : finiteEnergyMaximum I f ≤ finiteEnergyMaximum I g := by
  apply finiteEnergyMaximum_le I f (finiteEnergyMaximum_nonneg I g)
  intro j hj
  exact (h j hj).trans (le_finiteEnergyMaximum I g hj)

theorem finiteEnergyMaximum_empty {ι : Type*} (f : ι → ℝ) :
    finiteEnergyMaximum (∅ : Finset ι) f = 0 := by
  simp [finiteEnergyMaximum]

def profileOccupiedCellPairs (ρ : Measure Plane) (a : ℕ) :
    Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)) :=
  (occupiedUnitCells ρ a).product (occupiedUnitCells ρ a)

def profileSeparatedCellPairs (ρ : Measure Plane) (a : ℕ) :
    Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)) :=
  (profileOccupiedCellPairs ρ a).filter (fun P ↦ SeparatedDyadicCells a P.1 P.2)

/-- The genuine discrepancy state: the maximum of Definition 7.2 on actual separated cells. -/
def profileDistanceStateEnergy (ρ : Measure Plane) (A : ℕ → ℝ) (q N : ℕ) (E : ℝ)
    (levels i a t : ℕ) : ℝ :=
  finiteEnergyMaximum (profileSeparatedCellPairs ρ a) fun P ↦
    scheduledDistanceEnergy ρ ρ (dyadicCube a P.1) (dyadicCube a P.2) E
      (directionalLevelWidth levels i) (profileScheduledTests A q N a t)
      (profileScheduledTests A q N a t) t

/-- The genuine Fourier state: all actual occupied cells and the concrete remaining symbol class. -/
def profileFourierStateEnergy (ρ : Measure Plane) (A : ℕ → ℝ) (q N : ℕ) (E : ℝ)
    (levels i K k₀ cutoffK b e a v : ℕ) : ℝ :=
  finiteEnergyMaximum (profileOccupiedCellPairs ρ a) fun P ↦
    scheduledFourierEnergySup ρ ρ (dyadicCube a P.1) (dyadicCube a P.2) E
      (directionalLevelWidth levels i) K (profileRemainingTests A q N b e a)
      (profileRemainingTests A q N b e a) k₀ cutoffK v

/-- The analytic value attached to each literal combinatorial state, with actual measure excess. -/
def regularMeasureStateEnergy (ρ : Measure Plane) (θ : ℝ) (N i : ℕ) : ProfileChainState → ℝ
  | .discrepancy a t => profileDistanceStateEnergy ρ (regularMeasureExcess ρ N)
      (blockCount θ N) N (tolerance θ N * N) (maskLevelCount θ N) i a t
  | .fourier b e a v => profileFourierStateEnergy ρ (regularMeasureExcess ρ N)
      (blockCount θ N) N (tolerance θ N * N) (maskLevelCount θ N) i
      (8 * expansionCount θ N) (2 * expansionCount θ N) (8 * expansionCount θ N) b e a v

theorem profileDistanceStateEnergy_nonneg (ρ : Measure Plane) (A : ℕ → ℝ)
    (q N : ℕ) (E : ℝ) (levels i a t : ℕ) :
    0 ≤ profileDistanceStateEnergy ρ A q N E levels i a t := finiteEnergyMaximum_nonneg _ _

theorem profileFourierStateEnergy_nonneg (ρ : Measure Plane) (A : ℕ → ℝ)
    (q N : ℕ) (E : ℝ) (levels i K k₀ cutoffK b e a v : ℕ) :
    0 ≤ profileFourierStateEnergy ρ A q N E levels i K k₀ cutoffK b e a v :=
  finiteEnergyMaximum_nonneg _ _

theorem regularMeasureStateEnergy_nonneg (ρ : Measure Plane) (θ : ℝ) (N i : ℕ)
    (s : ProfileChainState) : 0 ≤ regularMeasureStateEnergy ρ θ N i s := by
  cases s
  · exact profileDistanceStateEnergy_nonneg ..
  · exact profileFourierStateEnergy_nonneg ..

end FalconerThetaGauge
