module

public import FalconerThetaGauge.ScheduledSymbolEnergy

/-! # The actual built-symbol supremum obeys the manuscript's cell excess bound -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem scheduledFourierEnergySup_cells_le_excess (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {N : ℕ} (hN : 0 < N)
    (a : ℕ) (P Q : Fin 2 → ℤ) (E width : ℝ) (K : ℕ)
    (I₁ I₂ : Finset ProfileScheduleTest) {k₀ : ℕ} (hk : k₀ ≤ K) (cutoffK v : ℕ) :
    scheduledFourierEnergySup ρ ρ (dyadicCube a P) (dyadicCube a Q) E width K I₁ I₂
        k₀ cutoffK v ≤
      2600 * (4 : ℝ) ^ ((v : ℝ) - a) *
        (2 : ℝ) ^ (-2 * N * regularMeasureExcess ρ N a) := by
  apply csSup_le (scheduledFourierEnergyValues_nonempty ρ ρ _ _ E width K I₁ I₂ k₀ cutoffK v)
  rintro z ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  exact maskedFourierEnergy_cells_le_excess ρ hρ hN a P Q
    (measurable_of_mem_scheduledSymbolClass ρ E width K I₁ k₀ hb₁)
    (measurable_of_mem_scheduledSymbolClass ρ E width K I₂ k₀ hb₂)
    (abs_le_one_of_mem_scheduledSymbolClass ρ E width K I₁ hk hb₁)
    (abs_le_one_of_mem_scheduledSymbolClass ρ E width K I₂ hk hb₂) cutoffK v

theorem scheduledFourierEnergySup_mono_order (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane) (E width : ℝ) (K : ℕ)
    (I₁ I₂ : Finset ProfileScheduleTest) {k₀ k₁ : ℕ} (horder : k₀ ≤ k₁) (hk : k₁ ≤ K)
    (cutoffK v : ℕ) :
    scheduledFourierEnergySup ρ₁ ρ₂ X Y E width K I₁ I₂ k₀ cutoffK v ≤
      scheduledFourierEnergySup ρ₁ ρ₂ X Y E width K I₁ I₂ k₁ cutoffK v := by
  apply csSup_le (scheduledFourierEnergyValues_nonempty ρ₁ ρ₂ X Y E width K I₁ I₂ k₀ cutoffK v)
  rintro z ⟨b₁, ⟨d₁, ho₁, rfl⟩, b₂, ⟨d₂, ho₂, rfl⟩, rfl⟩
  exact maskedFourierEnergy_le_scheduledFourierEnergySup ρ₁ ρ₂ X Y E width K I₁ I₂ hk cutoffK v
    ⟨d₁, ho₁.trans horder, rfl⟩ ⟨d₂, ho₂.trans horder, rfl⟩

end FalconerThetaGauge
