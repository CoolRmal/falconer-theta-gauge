/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularFilteredMeasureMixture

/-! # The actual retained-piece decomposition with its original mass weights -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical ENNReal

namespace FalconerThetaGauge

abbrev RegularRetainedType (μ : Measure Plane) (θ : ℝ) (N : ℕ) :=
  {t // t ∈ regularDyadicKeptTypes μ (tolerance θ N) (blockParameter θ N) N}

def regularRetainedCarrier (μ : Measure Plane) (θ : ℝ) (N : ℕ)
    (t : RegularRetainedType μ θ N) : Set Plane :=
  regularDyadicPartCarrier μ (tolerance θ N) N t.val

def regularRetainedMass (μ : Measure Plane) (θ : ℝ) (N : ℕ)
    (t : RegularRetainedType μ θ N) : ℝ≥0∞ := μ (regularRetainedCarrier μ θ N t)

def regularRetainedProbability (μ : Measure Plane) (θ : ℝ) (N : ℕ)
    (t : RegularRetainedType μ θ N) : Measure Plane :=
  regularDyadicPartMeasure μ (tolerance θ N) N t.val

def regularRetainedSymbol (μ : Measure Plane) (θ : ℝ) (N K : ℕ)
    (t : RegularRetainedType μ θ N) : Plane → UnitCircle → ℝ :=
  let ρ := regularRetainedProbability μ θ N t
  ScheduledSymbolData.maskProduct.symbol ρ (tolerance θ N * N) 2 K
    (regularMeasurePieceTests ρ θ N)

/-- The finite filter is literal for every chosen finite bump order. -/
def regularFilteredDistanceMeasure (μ ν : Measure Plane)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) (K : ℕ) : Measure ℝ :=
  finiteTestFilteredDistanceMeasure μ ν
    (regularDirectionalFilter μ hpar K) (regularDirectionalFilter ν hpar K)

theorem measurableSet_regularRetainedCarrier (μ : Measure Plane) (θ : ℝ) (N : ℕ)
    (t : RegularRetainedType μ θ N) : MeasurableSet (regularRetainedCarrier μ θ N t) :=
  measurableSet_regularDyadicPartCarrier μ (tolerance θ N) N t.val

theorem regularRetainedCarrier_pairwiseDisjoint (μ : Measure Plane) (θ : ℝ) (N : ℕ) :
    Pairwise (Disjoint on regularRetainedCarrier μ θ N) := by
  intro t u htu
  exact regularDyadicPartCarrier_disjoint μ (tolerance θ N) N
    (fun h ↦ htu (Subtype.ext h))

theorem regularRetainedMass_ne_zero (μ : Measure Plane) [IsProbabilityMeasure μ]
    (θ : ℝ) (N : ℕ) (t : RegularRetainedType μ θ N) :
    regularRetainedMass μ θ N t ≠ 0 := by
  have h := regularDyadicPartCarrier_mass_pos μ (tolerance θ N) (blockParameter θ N)
    N t.property
  intro hz
  have hz' : μ.real (regularDyadicPartCarrier μ (tolerance θ N) N t.val) = 0 := by
    change (regularRetainedMass μ θ N t).toReal = 0
    rw [hz, ENNReal.toReal_zero]
  exact (ne_of_gt h) hz'

theorem regularRetainedProbability_probability (μ : Measure Plane) [IsProbabilityMeasure μ]
    (θ : ℝ) (N : ℕ) (t : RegularRetainedType μ θ N) :
    IsProbabilityMeasure (regularRetainedProbability μ θ N t) :=
  (regularDyadicPartMeasure_probability μ (tolerance θ N) (blockParameter θ N)
    N t.property).1

theorem regularFilterCarrier_eq_iUnion (μ : Measure Plane) (θ : ℝ) (N : ℕ) :
    regularFilterCarrier μ θ N = ⋃ t : RegularRetainedType μ θ N,
      regularRetainedCarrier μ θ N t := by
  ext x
  simp only [regularFilterCarrier, regularRetainedCarrier, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨t, ht, hx⟩
    exact ⟨⟨t, ht⟩, hx⟩
  · rintro ⟨t, hx⟩
    exact ⟨t.val, t.property, hx⟩

theorem regularDirectionalFilter_symbol_eq_retainedSymbol (μ : Measure Plane)
    [IsProbabilityMeasure μ] {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) (K : ℕ)
    (t : RegularRetainedType μ θ N) {x : Plane} (hx : x ∈ regularRetainedCarrier μ θ N t)
    (w : UnitCircle) :
    (regularDirectionalFilter μ hpar K).symbol x w = regularRetainedSymbol μ θ N K t x w := by
  rw [regularDirectionalFilter_symbol_eq_piece_product μ hpar K t hx]
  rw [regularRetainedSymbol, ScheduledSymbolData.maskProduct_symbol]
  rfl

theorem regularDirectionalFilter_symbol_eq_zero_off_carrier (μ : Measure Plane)
    [IsProbabilityMeasure μ] {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) (K : ℕ)
    {x : Plane} (hx : x ∉ regularFilterCarrier μ θ N) (w : UnitCircle) :
    (regularDirectionalFilter μ hpar K).symbol x w = 0 := by
  unfold FiniteDirectionalFilter.symbol carrierDirectionalSymbol
  rw [regularDirectionalFilter_carrier μ hpar K]
  simp only [ite_eq_right hx]

/-- Every coefficient in the exact mixture is the original piece mass. -/
theorem regularFilteredDistanceMeasure_eq_piece_mixture (μ ν : Measure Plane)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) (K : ℕ) :
    regularFilteredDistanceMeasure μ ν hpar K =
      Measure.sum (fun p : RegularRetainedType μ θ N × RegularRetainedType ν θ N ↦
        (regularRetainedMass μ θ N p.1 * regularRetainedMass ν θ N p.2) •
          filteredCrossDistanceMeasure
            (regularRetainedProbability μ θ N p.1) (regularRetainedProbability ν θ N p.2)
            (directionalPairMask (regularRetainedSymbol μ θ N K p.1)
              (regularRetainedSymbol ν θ N K p.2))) := by
  let m := directionalPairMask (regularDirectionalFilter μ hpar K).symbol
    (regularDirectionalFilter ν hpar K).symbol
  let mij := fun t u ↦ directionalPairMask (regularRetainedSymbol μ θ N K t)
    (regularRetainedSymbol ν θ N K u)
  have hoff : ∀ p, p ∉
      (⋃ t : RegularRetainedType μ θ N, regularRetainedCarrier μ θ N t) ×ˢ
      (⋃ u : RegularRetainedType ν θ N, regularRetainedCarrier ν θ N u) → m p = 0 := by
    intro p hp
    rw [← regularFilterCarrier_eq_iUnion, ← regularFilterCarrier_eq_iUnion] at hp
    simp only [mem_prod, not_and_or] at hp
    rcases hp with hx | hy
    · simp [m, directionalPairMask,
        regularDirectionalFilter_symbol_eq_zero_off_carrier μ hpar K hx]
    · simp [m, directionalPairMask,
        regularDirectionalFilter_symbol_eq_zero_off_carrier ν hpar K hy]
  have hon : ∀ t u x, x ∈ regularRetainedCarrier μ θ N t →
      ∀ y, y ∈ regularRetainedCarrier ν θ N u → m (x, y) = mij t u (x, y) := by
    intro t u x hx y hy
    simp only [m, mij, directionalPairMask,
      regularDirectionalFilter_symbol_eq_retainedSymbol μ hpar K t hx,
      regularDirectionalFilter_symbol_eq_retainedSymbol ν hpar K u hy]
  have h := filteredCrossDistanceMeasure_finite_carrier_mixture μ ν
    (regularRetainedCarrier μ θ N) (regularRetainedCarrier ν θ N)
    (measurableSet_regularRetainedCarrier μ θ N)
    (measurableSet_regularRetainedCarrier ν θ N)
    (regularRetainedCarrier_pairwiseDisjoint μ θ N)
    (regularRetainedCarrier_pairwiseDisjoint ν θ N)
    (regularRetainedMass_ne_zero μ θ N) (regularRetainedMass_ne_zero ν θ N)
    m mij hoff hon
  exact h

theorem sum_regularRetainedMass_le_one (μ : Measure Plane) [IsProbabilityMeasure μ]
    (θ : ℝ) (N : ℕ) :
    ∑ t : RegularRetainedType μ θ N, regularRetainedMass μ θ N t ≤ 1 := by
  calc
    _ = μ (⋃ t : RegularRetainedType μ θ N, regularRetainedCarrier μ θ N t) := by
      rw [measure_iUnion (regularRetainedCarrier_pairwiseDisjoint μ θ N)
        (measurableSet_regularRetainedCarrier μ θ N), tsum_fintype]
      rfl
    _ ≤ μ Set.univ := measure_mono (subset_univ _)
    _ = 1 := measure_univ

end FalconerThetaGauge
