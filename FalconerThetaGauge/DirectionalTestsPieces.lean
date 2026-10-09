/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.DirectionalTestsPiecesCoverage

/-! # The actual finite directional filter on all retained regular pieces -/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeSeparatedMeasures

theorem regularPieceDirectionalFilter_pairwiseDisjoint
    (μ : Measure Plane) [IsProbabilityMeasure μ] {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) (K : ℕ) :
    ((Finset.univ : Finset
      {t // t ∈ regularDyadicKeptTypes μ (tolerance θ N) (blockParameter θ N) N}) :
      Set _).PairwiseDisjoint
      (fun t => (regularPieceDirectionalFilter μ hpar K t).carrier) := by
  intro t _ u _ htu
  change Disjoint (regularDyadicPartCarrier μ (tolerance θ N) N t.val)
    (regularDyadicPartCarrier μ (tolerance θ N) N u.val)
  exact regularDyadicPartCarrier_disjoint μ (tolerance θ N) N
    (fun h => htu (Subtype.ext h))

/-- Every retained original type supplies its own true probability, entry list and tests.
They share `N²+1` slots because a pin belongs to exactly one disjoint piece. -/
def regularDirectionalFilter (μ : Measure Plane) [IsProbabilityMeasure μ]
    {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) (K : ℕ) :
    FiniteDirectionalFilter N (tolerance θ N * N) :=
  assembleDirectionalFilters Finset.univ (regularPieceDirectionalFilter μ hpar K)
    (regularPieceDirectionalFilter_pairwiseDisjoint μ hpar K)

theorem regularDirectionalFilter_carrier (μ : Measure Plane) [IsProbabilityMeasure μ]
    {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) (K : ℕ) :
    (regularDirectionalFilter μ hpar K).carrier = regularFilterCarrier μ θ N := by
  ext x
  change x ∈ pieceFilterCarrier Finset.univ (regularPieceDirectionalFilter μ hpar K) ↔
    x ∈ regularFilterCarrier μ θ N
  simp only [pieceFilterCarrier, Finset.mem_univ, true_and, regularPieceDirectionalFilter_carrier,
    regularFilterCarrier, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨t, hx⟩
    exact ⟨t.val, t.property, hx⟩
  · rintro ⟨t, ht, hx⟩
    exact ⟨⟨t, ht⟩, hx⟩

theorem regularDirectionalFilter_testCount (μ : Measure Plane) [IsProbabilityMeasure μ]
    {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) (K : ℕ) :
    (regularDirectionalFilter μ hpar K).testCount = N ^ 2 + 1 := rfl

/-- The global symbol restricts exactly to the original local product, with neutral padding. -/
theorem regularDirectionalFilter_symbol_on_piece (μ : Measure Plane) [IsProbabilityMeasure μ]
    {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) (K : ℕ)
    (t : {t // t ∈ regularDyadicKeptTypes μ (tolerance θ N) (blockParameter θ N) N})
    {x : Plane} (hx : x ∈ regularDyadicPartCarrier μ (tolerance θ N) N t.val)
    (w : UnitCircle) :
    (regularDirectionalFilter μ hpar K).symbol x w =
      (regularPieceDirectionalFilter μ hpar K t).symbol x w :=
  assembleDirectionalFilters_symbol_on_piece
    (regularPieceDirectionalFilter_pairwiseDisjoint μ hpar K) (Finset.mem_univ t) hx w

/-- The literal filtered weighted distance measure, with the source's actual piece lists. -/
def scheduledFilteredDistanceMeasure (μ ν : Measure Plane)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) : Measure ℝ :=
  finiteTestFilteredDistanceMeasure μ ν
    (regularDirectionalFilter μ hpar (6 * expansionCount θ N))
    (regularDirectionalFilter ν hpar (6 * expansionCount θ N))

/-- Lemma 6.13 for the actual retained pieces, their finite scheduled tests and their masks. -/
theorem scheduledFilteredDistanceMeasure_mass_loss (μ ν : Measure Plane)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {θ K : ℝ} (hθ : 2 / 3 < θ) (hK : 0 ≤ K) {N : ℕ} (hpar : ParameterFacts θ N)
    (hunit₁ : μ unitSquare = 1) (hunit₂ : ν unitSquare = 1)
    {S₁ S₂ : Set Plane} (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂)
    (hμ : μ S₁ = 1) (hν : ν S₂ = 1)
    (hsep : ∀ x ∈ S₁, ∀ y ∈ S₂, (24 / 100 : ℝ) ≤ dist x y)
    (hpin₁ : ∀ x ∈ S₁,
      circleArcLength.withDensity (radialProjectionDensity ν x) = ν.map (radialProjection x) ∧
      radialOrliczMoment ν 8 x ≤ ENNReal.ofReal K)
    (hpin₂ : ∀ y ∈ S₂,
      circleArcLength.withDensity (radialProjectionDensity μ y) = μ.map (radialProjection y) ∧
      radialOrliczMoment μ 8 y ≤ ENNReal.ofReal K) :
    scheduledFilteredDistanceMeasure μ ν hpar ≤ weightedCrossDistanceMeasure μ ν ∧
    weightedCrossDistanceMeasure μ ν Set.univ - scheduledFilteredDistanceMeasure μ ν hpar Set.univ ≤
      ENNReal.ofReal (weightedFilterMassError θ K N) ∧
    Summable (weightedFilterMassError θ K) :=
  finiteTestFilteredDistanceMeasure_regular_mass_loss μ ν hθ hK hpar hunit₁ hunit₂
    hS₁ hS₂ hμ hν hsep _ _
    (regularDirectionalFilter_carrier μ hpar _) (regularDirectionalFilter_carrier ν hpar _)
    hpin₁ hpin₂

end FalconerThetaGauge
