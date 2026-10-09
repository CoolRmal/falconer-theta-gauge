/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.MaskedFourierEnergyCauchySchwarz

/-! # Genuine separation of the two prepared pieces' symbol energy suprema -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter

namespace FalconerThetaGauge

theorem scheduledFourierEnergySup_le_sqrt_self (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    (E width : ℝ) (K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest) {k₀ : ℕ}
    (hk : k₀ ≤ K) (cutoffK v : ℕ) :
    scheduledFourierEnergySup ρ₁ ρ₂ X Y E width K I₁ I₂ k₀ cutoffK v ≤
      Real.sqrt (scheduledFourierEnergySup ρ₁ ρ₁ X X E width K I₁ I₁ k₀ cutoffK v) *
        Real.sqrt
          (scheduledFourierEnergySup ρ₂ ρ₂ Y Y E width K I₂ I₂ k₀ cutoffK v) := by
  apply csSup_le (scheduledFourierEnergyValues_nonempty ρ₁ ρ₂ X Y E width
    K I₁ I₂ k₀ cutoffK v)
  rintro z ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  calc
    _ ≤ Real.sqrt (maskedFourierEnergy ρ₁ ρ₁ X X b₁ b₁ cutoffK v) *
        Real.sqrt (maskedFourierEnergy ρ₂ ρ₂ Y Y b₂ b₂ cutoffK v) :=
      maskedFourierEnergy_le_sqrt_self ρ₁ ρ₂ X Y
        (measurable_of_mem_scheduledSymbolClass ρ₁ E width K I₁ k₀ hb₁)
        (measurable_of_mem_scheduledSymbolClass ρ₂ E width K I₂ k₀ hb₂)
        (abs_le_one_of_mem_scheduledSymbolClass ρ₁ E width K I₁ hk hb₁)
        (abs_le_one_of_mem_scheduledSymbolClass ρ₂ E width K I₂ hk hb₂) cutoffK v
    _ ≤ _ := by
      gcongr
      · exact maskedFourierEnergy_le_scheduledFourierEnergySup ρ₁ ρ₁ X X E width K
          I₁ I₁ hk cutoffK v hb₁ hb₁
      · exact maskedFourierEnergy_le_scheduledFourierEnergySup ρ₂ ρ₂ Y Y E width K
          I₂ I₂ hk cutoffK v hb₂ hb₂

theorem maskedCircularSpectrum_probability_carrier_eq (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] {S T : Set Plane} (hS : MeasurableSet S)
    (hT : MeasurableSet T) (hρS : ρ S = 1) (hρT : ρ T = 1)
    (b : Plane → UnitCircle → ℝ) :
    maskedCircularSpectrum ρ S b = maskedCircularSpectrum ρ T b := by
  funext r
  simp only [maskedCircularSpectrum, maskedFourierAmplitude, Measure.real,
    restrict_eq_self_of_probability_mass_one ρ hS hρS,
    restrict_eq_self_of_probability_mass_one ρ hT hρT, hρS, hρT]

theorem maskedFourierEnergy_probability_carrier_eq (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] {S T : Set Plane} (hS : MeasurableSet S)
    (hT : MeasurableSet T) (hρS : ρ S = 1) (hρT : ρ T = 1)
    (b₁ b₂ : Plane → UnitCircle → ℝ) (K v : ℕ) :
    maskedFourierEnergy ρ ρ S S b₁ b₂ K v = maskedFourierEnergy ρ ρ T T b₁ b₂ K v := by
  simp only [maskedFourierEnergy,
    maskedCircularSpectrum_probability_carrier_eq ρ hS hT hρS hρT b₁,
    maskedCircularSpectrum_probability_carrier_eq ρ hS hT hρS hρT b₂]

theorem scheduledFourierEnergySup_probability_carrier_eq (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] {S T : Set Plane} (hS : MeasurableSet S)
    (hT : MeasurableSet T) (hρS : ρ S = 1) (hρT : ρ T = 1)
    (E width : ℝ) (K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest) (k₀ cutoffK v : ℕ) :
    scheduledFourierEnergySup ρ ρ S S E width K I₁ I₂ k₀ cutoffK v =
      scheduledFourierEnergySup ρ ρ T T E width K I₁ I₂ k₀ cutoffK v := by
  simp only [scheduledFourierEnergySup, scheduledFourierEnergyValues,
    maskedFourierEnergy_probability_carrier_eq ρ hS hT hρS hρT]

end FalconerThetaGauge
