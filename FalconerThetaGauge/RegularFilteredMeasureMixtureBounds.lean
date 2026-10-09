/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularFilteredMeasureMixtureFourier

/-! # The genuine global annulus bound from the actual regular-piece energies -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Metric
open scoped Classical ENNReal

namespace FalconerThetaGauge

def regularRetainedPairMeasure (μ ν : Measure Plane) (θ : ℝ) (N K : ℕ)
    (p : RegularRetainedType μ θ N × RegularRetainedType ν θ N) : Measure ℝ :=
  filteredCrossDistanceMeasure
    (regularRetainedProbability μ θ N p.1) (regularRetainedProbability ν θ N p.2)
    (directionalPairMask (regularRetainedSymbol μ θ N K p.1)
      (regularRetainedSymbol ν θ N K p.2))

def regularRetainedPairMass (μ ν : Measure Plane) (θ : ℝ) (N : ℕ)
    (p : RegularRetainedType μ θ N × RegularRetainedType ν θ N) : ℝ≥0∞ :=
  regularRetainedMass μ θ N p.1 * regularRetainedMass ν θ N p.2

theorem regularRetainedMass_ne_top (μ : Measure Plane) [IsProbabilityMeasure μ]
    (θ : ℝ) (N : ℕ) (t : RegularRetainedType μ θ N) :
    regularRetainedMass μ θ N t ≠ ∞ := measure_ne_top μ _

theorem sum_regularRetainedMass_toReal_le_one (μ : Measure Plane) [IsProbabilityMeasure μ]
    (θ : ℝ) (N : ℕ) :
    ∑ t : RegularRetainedType μ θ N, (regularRetainedMass μ θ N t).toReal ≤ 1 := by
  have hsum := sum_regularRetainedMass_le_one μ θ N
  have hfin : (∑ t : RegularRetainedType μ θ N, regularRetainedMass μ θ N t) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr
    (fun t _ ↦ regularRetainedMass_ne_top μ θ N t)
  have h := (ENNReal.toReal_le_toReal hfin (by simp)).mpr hsum
  rw [ENNReal.toReal_sum (fun t _ ↦ regularRetainedMass_ne_top μ θ N t),
    ENNReal.toReal_one] at h
  exact h

theorem regularRetainedPairMass_ne_top (μ ν : Measure Plane)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (θ : ℝ) (N : ℕ)
    (p : RegularRetainedType μ θ N × RegularRetainedType ν θ N) :
    regularRetainedPairMass μ ν θ N p ≠ ∞ :=
  ENNReal.mul_ne_top (regularRetainedMass_ne_top μ θ N p.1)
    (regularRetainedMass_ne_top ν θ N p.2)

theorem sum_regularRetainedPairMass_toReal_le_one (μ ν : Measure Plane)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (θ : ℝ) (N : ℕ) :
    ∑ p : RegularRetainedType μ θ N × RegularRetainedType ν θ N,
      (regularRetainedPairMass μ ν θ N p).toReal ≤ 1 := by
  simp only [regularRetainedPairMass, ENNReal.toReal_mul, Fintype.sum_prod_type]
  rw [← Finset.sum_mul_sum]
  exact (mul_le_mul (sum_regularRetainedMass_toReal_le_one μ θ N)
    (sum_regularRetainedMass_toReal_le_one ν θ N)
    (Finset.sum_nonneg fun _ _ ↦ ENNReal.toReal_nonneg) (by norm_num)).trans_eq (one_mul _)

theorem regularRetainedSymbol_mem_Icc (μ : Measure Plane) (θ : ℝ) (N K : ℕ)
    (t : RegularRetainedType μ θ N) (x : Plane) (w : UnitCircle) :
    regularRetainedSymbol μ θ N K t x w ∈ Icc 0 1 := by
  unfold regularRetainedSymbol
  rw [ScheduledSymbolData.maskProduct_symbol]
  exact scheduledWidthMaskProduct_mem_Icc _ _ _ _ _ _ _

theorem isFiniteMeasure_regularRetainedPairMeasure (μ ν : Measure Plane)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (θ : ℝ) (N K : ℕ)
    {S T : Set Plane} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hμ : μ S = 1) (hν : ν T = 1) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ x ∈ S, ∀ y ∈ T, d ≤ dist x y)
    (p : RegularRetainedType μ θ N × RegularRetainedType ν θ N) :
    IsFiniteMeasure (regularRetainedPairMeasure μ ν θ N K p) := by
  let ρ₁ := regularRetainedProbability μ θ N p.1
  let ρ₂ := regularRetainedProbability ν θ N p.2
  let : IsProbabilityMeasure ρ₁ := regularRetainedProbability_probability μ θ N p.1
  let : IsProbabilityMeasure ρ₂ := regularRetainedProbability_probability ν θ N p.2
  have hρ₁ := regularDyadicPartMeasure_mass_one μ hS hμ
    (tolerance θ N) (blockParameter θ N) N p.1.property
  have hρ₂ := regularDyadicPartMeasure_mass_one ν hT hν
    (tolerance θ N) (blockParameter θ N) N p.2.property
  have hrest₁ : ρ₁.restrict S = ρ₁ :=
    restrict_eq_self_of_probability_mass_one ρ₁ hS hρ₁
  have hrest₂ : ρ₂.restrict T = ρ₂ :=
    restrict_eq_self_of_probability_mass_one ρ₂ hT hρ₂
  have hi := isFiniteMeasure_maskedDistance ρ₁ ρ₂ hS hT hd hsep
    (regularRetainedSymbol_mem_Icc μ θ N K p.1)
    (regularRetainedSymbol_mem_Icc ν θ N K p.2)
  simpa only [hrest₁, hrest₂, regularRetainedPairMeasure, ρ₁, ρ₂] using hi

/-- The global filter's literal annulus is bounded by the original weighted piece annuli. -/
theorem regularFilteredDistanceMeasure_annulus_le_piece_annuli (μ ν : Measure Plane)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) (K : ℕ)
    {S T : Set Plane} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hμ : μ S = 1) (hν : ν T = 1) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ x ∈ S, ∀ y ∈ T, d ≤ dist x y) (s t : ℝ) :
    scalarFourierAnnulusIntegral (regularFilteredDistanceMeasure μ ν hpar K) s t ≤
      ∑ p : RegularRetainedType μ θ N × RegularRetainedType ν θ N,
        (regularRetainedPairMass μ ν θ N p).toReal *
          scalarFourierAnnulusIntegral (regularRetainedPairMeasure μ ν θ N K p) s t := by
  let : ∀ p, IsFiniteMeasure (regularRetainedPairMeasure μ ν θ N K p) :=
    isFiniteMeasure_regularRetainedPairMeasure μ ν θ N K hS hT hμ hν hd hsep
  rw [regularFilteredDistanceMeasure_eq_piece_mixture]
  exact scalarFourierAnnulusIntegral_subprobability_mixture_le
    (regularRetainedPairMeasure μ ν θ N K) (regularRetainedPairMass μ ν θ N)
    (regularRetainedPairMass_ne_top μ ν θ N)
    (sum_regularRetainedPairMass_toReal_le_one μ ν θ N) s t

end FalconerThetaGauge
