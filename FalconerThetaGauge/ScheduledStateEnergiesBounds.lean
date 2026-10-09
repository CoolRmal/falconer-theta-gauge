module

public import FalconerThetaGauge.ScheduledStateEnergies

/-! # Literal cell bounds and membership inequalities for the actual analytic induction states -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem scheduledDistanceEnergy_le_profileDistanceStateEnergy (ρ : Measure Plane)
    (A : ℕ → ℝ) (q N : ℕ) (E : ℝ) (levels i a t : ℕ) {P Q : Fin 2 → ℤ}
    (hP : P ∈ occupiedUnitCells ρ a) (hQ : Q ∈ occupiedUnitCells ρ a)
    (hsep : SeparatedDyadicCells a P Q) :
    scheduledDistanceEnergy ρ ρ (dyadicCube a P) (dyadicCube a Q) E
        (directionalLevelWidth levels i) (profileScheduledTests A q N a t)
        (profileScheduledTests A q N a t) t ≤
      profileDistanceStateEnergy ρ A q N E levels i a t := by
  unfold profileDistanceStateEnergy
  apply le_finiteEnergyMaximum (profileSeparatedCellPairs ρ a)
    (fun R ↦ scheduledDistanceEnergy ρ ρ (dyadicCube a R.1) (dyadicCube a R.2) E
      (directionalLevelWidth levels i) (profileScheduledTests A q N a t)
      (profileScheduledTests A q N a t) t) (j := (P, Q))
  exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hP, hQ⟩, hsep⟩

theorem maskedFourierEnergy_le_profileFourierStateEnergy (ρ : Measure Plane)
    [IsFiniteMeasure ρ] (A : ℕ → ℝ) (q N : ℕ) (E : ℝ)
    (levels i K : ℕ) {k₀ : ℕ} (hk : k₀ ≤ K) (cutoffK b e a v : ℕ)
    {P Q : Fin 2 → ℤ} (hP : P ∈ occupiedUnitCells ρ a) (hQ : Q ∈ occupiedUnitCells ρ a)
    {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ E (directionalLevelWidth levels i) K
      (profileRemainingTests A q N b e a) k₀)
    (hb₂ : b₂ ∈ scheduledSymbolClass ρ E (directionalLevelWidth levels i) K
      (profileRemainingTests A q N b e a) k₀) :
    maskedFourierEnergy ρ ρ (dyadicCube a P) (dyadicCube a Q) b₁ b₂ cutoffK v ≤
      profileFourierStateEnergy ρ A q N E levels i K k₀ cutoffK b e a v := by
  apply (maskedFourierEnergy_le_scheduledFourierEnergySup ρ ρ _ _ E _ K _ _ hk cutoffK v
    hb₁ hb₂).trans
  unfold profileFourierStateEnergy
  apply le_finiteEnergyMaximum (profileOccupiedCellPairs ρ a)
    (fun R ↦ scheduledFourierEnergySup ρ ρ (dyadicCube a R.1) (dyadicCube a R.2) E
      (directionalLevelWidth levels i) K (profileRemainingTests A q N b e a)
      (profileRemainingTests A q N b e a) k₀ cutoffK v) (j := (P, Q))
  exact Finset.mem_product.2 ⟨hP, hQ⟩

theorem profileDistanceStateEnergy_le_excess (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {N : ℕ} (hN : 0 < N) (A : ℕ → ℝ)
    (q : ℕ) (E : ℝ) (levels i a t : ℕ) :
    profileDistanceStateEnergy ρ A q N E levels i a t ≤
      (2 : ℝ) ^ ((t : ℝ) - a) * (2 : ℝ) ^ (-2 * N * regularMeasureExcess ρ N a) := by
  apply finiteEnergyMaximum_le _ _ (by positivity)
  intro P hP
  exact maskedDistanceEnergy_cells_le_excess ρ hρ hN (Finset.mem_filter.1 hP).2 _ t

theorem profileFourierStateEnergy_le_excess (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {N : ℕ} (hN : 0 < N) (A : ℕ → ℝ)
    (q : ℕ) (E : ℝ) (levels i K : ℕ) {k₀ : ℕ} (hk : k₀ ≤ K)
    (cutoffK b e a v : ℕ) :
    profileFourierStateEnergy ρ A q N E levels i K k₀ cutoffK b e a v ≤
      2600 * (4 : ℝ) ^ ((v : ℝ) - a) *
        (2 : ℝ) ^ (-2 * N * regularMeasureExcess ρ N a) := by
  apply finiteEnergyMaximum_le _ _ (by positivity)
  intro P hP
  exact scheduledFourierEnergySup_cells_le_excess ρ hρ hN a P.1 P.2 E _ K _ _ hk cutoffK v

theorem regularMeasureStateEnergy_discrepancy_le_excess (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) (θ : ℝ) {N : ℕ} (hN : 0 < N)
    (i a t : ℕ) :
    regularMeasureStateEnergy ρ θ N i (.discrepancy a t) ≤
      (2 : ℝ) ^ ((t : ℝ) - a) * (2 : ℝ) ^ (-2 * N * regularMeasureExcess ρ N a) :=
  profileDistanceStateEnergy_le_excess ρ hρ hN _ _ _ _ _ _ _

theorem regularMeasureStateEnergy_fourier_le_excess (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) (θ : ℝ) {N : ℕ} (hN : 0 < N)
    (i b e a v : ℕ) :
    regularMeasureStateEnergy ρ θ N i (.fourier b e a v) ≤
      2600 * (4 : ℝ) ^ ((v : ℝ) - a) *
        (2 : ℝ) ^ (-2 * N * regularMeasureExcess ρ N a) :=
  profileFourierStateEnergy_le_excess ρ hρ hN _ _ _ _ _ _ (by omega) _ _ _ _ _

/-- Refining the start removes exactly the newly reached masks from the actual Fourier list. -/
theorem profileRemainingTests_filter_deeper (A : ℕ → ℝ) (q N b e : ℕ) {a p : ℕ}
    (hap : a ≤ p) :
    (profileRemainingTests A q N b e a).filter (fun test ↦ p < test.anchor) =
      profileRemainingTests A q N b e p := by
  ext test
  simp only [profileRemainingTests, Finset.mem_filter]
  constructor
  · rintro ⟨⟨h, _⟩, hp⟩
    exact ⟨h, hp⟩
  · rintro ⟨h, hp⟩
    exact ⟨⟨h, hap.trans_lt hp⟩, hp⟩

end FalconerThetaGauge
