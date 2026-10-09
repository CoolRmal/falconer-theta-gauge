module

public import FalconerThetaGauge.ScheduledSymbolReached

/-! # Actual suprema of the literal built-symbol Fourier energies used in the recurrences -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical ContDiff

namespace FalconerThetaGauge

open GaugeFrostman

theorem measurable_of_mem_scheduledSymbolClass (ρ : Measure Plane) (E width : ℝ)
    (K : ℕ) (I : Finset ProfileScheduleTest) (k₀ : ℕ) {b : Plane → UnitCircle → ℝ}
    (hb : b ∈ scheduledSymbolClass ρ E width K I k₀) : Measurable (uncurry b) := by
  obtain ⟨d, _, rfl⟩ := hb
  exact d.measurable_symbol ρ E width K I

/-- The values are actual integrals for every pair in Definition 6.10's concrete symbol classes. -/
def scheduledFourierEnergyValues (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane) (E width : ℝ)
    (K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest) (k₀ cutoffK v : ℕ) : Set ℝ :=
  {z | ∃ b₁ ∈ scheduledSymbolClass ρ₁ E width K I₁ k₀,
    ∃ b₂ ∈ scheduledSymbolClass ρ₂ E width K I₂ k₀,
      z = maskedFourierEnergy ρ₁ ρ₂ X Y b₁ b₂ cutoffK v}

def scheduledFourierEnergySup (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane) (E width : ℝ)
    (K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest) (k₀ cutoffK v : ℕ) : ℝ :=
  sSup (scheduledFourierEnergyValues ρ₁ ρ₂ X Y E width K I₁ I₂ k₀ cutoffK v)

theorem scheduledFourierEnergyValues_nonempty (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    (E width : ℝ) (K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest) (k₀ cutoffK v : ℕ) :
    (scheduledFourierEnergyValues ρ₁ ρ₂ X Y E width K I₁ I₂ k₀ cutoffK v).Nonempty :=
  ⟨_, _, scheduledWidthMaskProduct_mem_symbolClass ρ₁ E width K I₁ k₀,
    _, scheduledWidthMaskProduct_mem_symbolClass ρ₂ E width K I₂ k₀, rfl⟩

theorem scheduledFourierEnergyValues_bddAbove (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane) (E width : ℝ) (K : ℕ)
    (I₁ I₂ : Finset ProfileScheduleTest) {k₀ : ℕ} (hk : k₀ ≤ K) (cutoffK v : ℕ) :
    BddAbove (scheduledFourierEnergyValues ρ₁ ρ₂ X Y E width K I₁ I₂ k₀ cutoffK v) := by
  refine ⟨2600 * (4 : ℝ) ^ v * (ρ₁.real X * ρ₂.real Y), ?_⟩
  rintro z ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  exact maskedFourierEnergy_le ρ₁ ρ₂ X Y
    (measurable_of_mem_scheduledSymbolClass ρ₁ E width K I₁ k₀ hb₁)
    (measurable_of_mem_scheduledSymbolClass ρ₂ E width K I₂ k₀ hb₂)
    (abs_le_one_of_mem_scheduledSymbolClass ρ₁ E width K I₁ hk hb₁)
    (abs_le_one_of_mem_scheduledSymbolClass ρ₂ E width K I₂ hk hb₂) cutoffK v

theorem maskedFourierEnergy_le_scheduledFourierEnergySup (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane) (E width : ℝ) (K : ℕ)
    (I₁ I₂ : Finset ProfileScheduleTest) {k₀ : ℕ} (hk : k₀ ≤ K) (cutoffK v : ℕ)
    {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ₁ E width K I₁ k₀)
    (hb₂ : b₂ ∈ scheduledSymbolClass ρ₂ E width K I₂ k₀) :
    maskedFourierEnergy ρ₁ ρ₂ X Y b₁ b₂ cutoffK v ≤
      scheduledFourierEnergySup ρ₁ ρ₂ X Y E width K I₁ I₂ k₀ cutoffK v :=
  le_csSup (scheduledFourierEnergyValues_bddAbove ρ₁ ρ₂ X Y E width K I₁ I₂ hk cutoffK v)
    ⟨b₁, hb₁, b₂, hb₂, rfl⟩

theorem scheduledFourierEnergySup_nonneg (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane) (E width : ℝ) (K : ℕ)
    (I₁ I₂ : Finset ProfileScheduleTest) {k₀ : ℕ} (hk : k₀ ≤ K) (cutoffK v : ℕ) :
    0 ≤ scheduledFourierEnergySup ρ₁ ρ₂ X Y E width K I₁ I₂ k₀ cutoffK v :=
  (maskedFourierEnergy_nonneg ρ₁ ρ₂ X Y _ _ cutoffK v).trans
    (maskedFourierEnergy_le_scheduledFourierEnergySup ρ₁ ρ₂ X Y E width K I₁ I₂ hk cutoffK v
      (scheduledWidthMaskProduct_mem_symbolClass ρ₁ E width K I₁ k₀)
      (scheduledWidthMaskProduct_mem_symbolClass ρ₂ E width K I₂ k₀))

theorem scheduledFourierEnergySup_le (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane) (E width : ℝ) (K : ℕ)
    (I₁ I₂ : Finset ProfileScheduleTest) {k₀ : ℕ} (hk : k₀ ≤ K) (cutoffK v : ℕ) :
    scheduledFourierEnergySup ρ₁ ρ₂ X Y E width K I₁ I₂ k₀ cutoffK v ≤
      2600 * (4 : ℝ) ^ v * (ρ₁.real X * ρ₂.real Y) := by
  apply csSup_le (scheduledFourierEnergyValues_nonempty ρ₁ ρ₂ X Y E width K I₁ I₂ k₀ cutoffK v)
  rintro z ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  exact maskedFourierEnergy_le ρ₁ ρ₂ X Y
    (measurable_of_mem_scheduledSymbolClass ρ₁ E width K I₁ k₀ hb₁)
    (measurable_of_mem_scheduledSymbolClass ρ₂ E width K I₂ k₀ hb₂)
    (abs_le_one_of_mem_scheduledSymbolClass ρ₁ E width K I₁ hk hb₁)
    (abs_le_one_of_mem_scheduledSymbolClass ρ₂ E width K I₂ hk hb₂) cutoffK v

/-- S4 holds for the true supremum over built symbols, not only for the mask product. -/
theorem scheduledFourierEnergySup_drop_reached (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (E width : ℝ) (K : ℕ)
    (I₁ I₂ : Finset ProfileScheduleTest) {k₀ : ℕ} (hk : k₀ ≤ K) (a : ℕ)
    {P Q : Fin 2 → ℤ} (hP : P ∈ occupiedUnitCells ρ₁ a) (hQ : Q ∈ occupiedUnitCells ρ₂ a)
    (cutoffK v : ℕ) :
    scheduledFourierEnergySup ρ₁ ρ₂ (dyadicCube a P) (dyadicCube a Q) E width K I₁ I₂
        k₀ cutoffK v ≤
      scheduledFourierEnergySup ρ₁ ρ₂ (dyadicCube a P) (dyadicCube a Q) E width K
        (I₁.filter (fun test ↦ a < test.anchor)) (I₂.filter (fun test ↦ a < test.anchor))
        k₀ cutoffK v := by
  apply csSup_le (scheduledFourierEnergyValues_nonempty ρ₁ ρ₂ _ _ E width K I₁ I₂ k₀ cutoffK v)
  rintro z ⟨b₁, ⟨d₁, ho₁, rfl⟩, b₂, ⟨d₂, ho₂, rfl⟩, rfl⟩
  apply (maskedFourierEnergy_builtSymbol_drop_reached d₁ d₂ ρ₁ ρ₂ E width K I₁ I₂
    (ho₁.trans hk) (ho₂.trans hk) a hP hQ cutoffK v).trans
  apply maskedFourierEnergy_le_scheduledFourierEnergySup ρ₁ ρ₂ _ _ E width K _ _ hk cutoffK v
  · exact ⟨d₁, (d₁.order_le_of_subset (Finset.filter_subset _ _)).trans ho₁, rfl⟩
  · exact ⟨d₂, (d₂.order_le_of_subset (Finset.filter_subset _ _)).trans ho₂, rfl⟩

end FalconerThetaGauge
