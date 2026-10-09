module

public import FalconerThetaGauge.ScheduledStateEnergiesBounds

/-! # Exact passage from refined occupied-cell symbol energies to the actual Fourier child state -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman

theorem scheduledFourierEnergySup_remaining_le_refined_state (ρ : Measure Plane)
    [IsFiniteMeasure ρ] (A : ℕ → ℝ) (q N : ℕ) (E : ℝ)
    (levels i K : ℕ) {k₀ : ℕ} (hk : k₀ ≤ K) (cutoffK b e : ℕ) {a p : ℕ}
    (hap : a ≤ p) (v : ℕ) {P Q : Fin 2 → ℤ}
    (hP : P ∈ occupiedUnitCells ρ p) (hQ : Q ∈ occupiedUnitCells ρ p) :
    scheduledFourierEnergySup ρ ρ (dyadicCube p P) (dyadicCube p Q) E
        (directionalLevelWidth levels i) K (profileRemainingTests A q N b e a)
        (profileRemainingTests A q N b e a) k₀ cutoffK v ≤
      profileFourierStateEnergy ρ A q N E levels i K k₀ cutoffK b e p v := by
  apply (scheduledFourierEnergySup_drop_reached ρ ρ E _ K _ _ hk p hP hQ cutoffK v).trans
  rw [profileRemainingTests_filter_deeper A q N b e hap]
  unfold profileFourierStateEnergy
  apply le_finiteEnergyMaximum (profileOccupiedCellPairs ρ p)
    (fun R ↦ scheduledFourierEnergySup ρ ρ (dyadicCube p R.1) (dyadicCube p R.2) E
      (directionalLevelWidth levels i) K (profileRemainingTests A q N b e p)
      (profileRemainingTests A q N b e p) k₀ cutoffK v) (j := (P, Q))
  exact Finset.mem_product.2 ⟨hP, hQ⟩

theorem maskedFourierEnergy_remaining_le_refined_state (d₁ d₂ : ScheduledSymbolData)
    (ρ : Measure Plane) [IsFiniteMeasure ρ] (A : ℕ → ℝ) (q N : ℕ) (E : ℝ)
    (levels i K : ℕ) {k₀ : ℕ} (hk : k₀ ≤ K) (cutoffK b e : ℕ) {a p : ℕ}
    (hap : a ≤ p) (v : ℕ) {P Q : Fin 2 → ℤ}
    (hP : P ∈ occupiedUnitCells ρ p) (hQ : Q ∈ occupiedUnitCells ρ p)
    (horder₁ : d₁.order (profileRemainingTests A q N b e a) ≤ k₀)
    (horder₂ : d₂.order (profileRemainingTests A q N b e a) ≤ k₀) :
    maskedFourierEnergy ρ ρ (dyadicCube p P) (dyadicCube p Q)
        (d₁.symbol ρ E (directionalLevelWidth levels i) K (profileRemainingTests A q N b e a))
        (d₂.symbol ρ E (directionalLevelWidth levels i) K (profileRemainingTests A q N b e a))
        cutoffK v ≤
      profileFourierStateEnergy ρ A q N E levels i K k₀ cutoffK b e p v :=
  (maskedFourierEnergy_le_scheduledFourierEnergySup ρ ρ _ _ E _ K _ _ hk cutoffK v
    ⟨d₁, horder₁, rfl⟩ ⟨d₂, horder₂, rfl⟩).trans
      (scheduledFourierEnergySup_remaining_le_refined_state ρ A q N E levels i K hk
        cutoffK b e hap v hP hQ)

end FalconerThetaGauge
