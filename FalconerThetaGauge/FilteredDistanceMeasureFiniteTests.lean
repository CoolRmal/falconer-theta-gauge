module

public import FalconerThetaGauge.FilteredDistanceMeasureParameters

/-!
# Lemma 6.13 for literal finite families of Borel tests

`FiniteDirectionalFilter` records concrete finite failure sets and concrete
finite mask functions, with their individual short-arc and passing-mask
properties. The removed pair mass is then proved, not assumed. Geometric
tube/projection tests can supply these fields after their construction.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerThetaGauge

/-- Concrete finite directional failure sets and mask functions at one scale. -/
structure FiniteDirectionalFilter (N : ℕ) (E : ℝ) where
  carrier : Set Plane
  carrier_measurable : MeasurableSet carrier
  testCount : ℕ
  testCount_le : testCount ≤ N ^ 2 + 1
  badTest : Fin testCount → Set (Plane × UnitCircle)
  badTest_measurable : ∀ i, MeasurableSet (badTest i)
  badTest_symmetric : ∀ i, IsSymmetricBadDirections (badTest i)
  badTest_short : ∀ i x, circleArcLength (badDirectionsAt (badTest i) x) ≤
    ENNReal.ofReal (2 * Real.pi * (2 : ℝ) ^ (-2 * E))
  maskTest : Fin testCount → Plane → UnitCircle → ℝ
  maskTest_measurable : ∀ i, Measurable (Function.uncurry (maskTest i))
  maskTest_range : ∀ i x w, maskTest i x w ∈ Icc 0 1
  maskTest_passing : ∀ i, ∀ x ∈ carrier, ∀ w, (x, w) ∉ badTest i → maskTest i x w = 1

/-- The actual finite union of this filter's test-failure sets. -/
def FiniteDirectionalFilter.badDirections {N : ℕ} {E : ℝ} (F : FiniteDirectionalFilter N E) :
    Set (Plane × UnitCircle) := finiteBadDirections Finset.univ F.badTest

/-- The actual product of this filter's masks, zero outside its regular carrier. -/
def FiniteDirectionalFilter.symbol {N : ℕ} {E : ℝ} (F : FiniteDirectionalFilter N E) :
    Plane → UnitCircle → ℝ := carrierDirectionalSymbol F.carrier Finset.univ F.maskTest

theorem FiniteDirectionalFilter.badDirections_measurable {N : ℕ} {E : ℝ}
    (F : FiniteDirectionalFilter N E) : MeasurableSet F.badDirections :=
  measurableSet_finiteBadDirections (fun i _ ↦ F.badTest_measurable i)

theorem FiniteDirectionalFilter.badDirections_symmetric {N : ℕ} {E : ℝ}
    (F : FiniteDirectionalFilter N E) : IsSymmetricBadDirections F.badDirections :=
  isSymmetricBadDirections_finiteBadDirections (fun i _ ↦ F.badTest_symmetric i)

theorem FiniteDirectionalFilter.badDirections_short {N : ℕ} {E : ℝ}
    (F : FiniteDirectionalFilter N E) (x : Plane) :
    circleArcLength (badDirectionsAt F.badDirections x) ≤
      ENNReal.ofReal (filterBadDirectionLength N E) := by
  have hcard : (Finset.univ : Finset (Fin F.testCount)).card ≤ N ^ 2 + 1 := by
    simpa using F.testCount_le
  exact circleArcLength_finiteBadDirections_le Finset.univ F.badTest N E hcard x
    (fun i _ ↦ F.badTest_short i x)

theorem FiniteDirectionalFilter.symbol_measurable {N : ℕ} {E : ℝ}
    (F : FiniteDirectionalFilter N E) : Measurable (Function.uncurry F.symbol) :=
  measurable_carrierDirectionalSymbol F.carrier_measurable
    (fun i _ ↦ F.maskTest_measurable i)

theorem FiniteDirectionalFilter.symbol_range {N : ℕ} {E : ℝ}
    (F : FiniteDirectionalFilter N E) (x : Plane) (w : UnitCircle) :
    F.symbol x w ∈ Icc 0 1 :=
  carrierDirectionalSymbol_mem_Icc _ _ (fun i _ ↦ F.maskTest_range i) x w

theorem FiniteDirectionalFilter.symbol_passing {N : ℕ} {E : ℝ}
    (F : FiniteDirectionalFilter N E) {x : Plane} (hx : x ∈ F.carrier) {w : UnitCircle}
    (hw : (x, w) ∉ F.badDirections) : F.symbol x w = 1 :=
  carrierDirectionalSymbol_eq_one_off_badDirections (fun i _ ↦ F.maskTest_passing i) hx hw

/-- The literal filtered measure of Definition 6.12 for the two finite test lists. -/
def finiteTestFilteredDistanceMeasure (μ ν : Measure Plane) {N : ℕ} {E : ℝ}
    (F₁ F₂ : FiniteDirectionalFilter N E) : Measure ℝ :=
  filteredCrossDistanceMeasure μ ν (directionalPairMask F₁.symbol F₂.symbol)

/-- Lemma 6.13, including its exact weighted mass error and full scale summability,
for the actual finite masks and short direction sets. -/
theorem finiteTestFilteredDistanceMeasure_mass_loss
    (μ ν : Measure Plane) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {θ K : ℝ} (hθ : 2 / 3 < θ) (hK : 0 ≤ K) {N : ℕ} (hpar : ParameterFacts θ N)
    {S₁ S₂ : Set Plane} (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂)
    (hμ : μ S₁ = 1) (hν : ν S₂ = 1)
    (hsep : ∀ x ∈ S₁, ∀ y ∈ S₂, (24 / 100 : ℝ) ≤ dist x y)
    (F₁ F₂ : FiniteDirectionalFilter N (tolerance θ N * N))
    (hdef₁ : μ F₁.carrierᶜ ≤
      ENNReal.ofReal (2 * (2 : ℝ) ^ (-(blockParameter θ N * N) / 4)))
    (hdef₂ : ν F₂.carrierᶜ ≤
      ENNReal.ofReal (2 * (2 : ℝ) ^ (-(blockParameter θ N * N) / 4)))
    (hpin₁ : ∀ x ∈ S₁,
      circleArcLength.withDensity (radialProjectionDensity ν x) = ν.map (radialProjection x) ∧
      radialOrliczMoment ν 8 x ≤ ENNReal.ofReal K)
    (hpin₂ : ∀ y ∈ S₂,
      circleArcLength.withDensity (radialProjectionDensity μ y) = μ.map (radialProjection y) ∧
      radialOrliczMoment μ 8 y ≤ ENNReal.ofReal K) :
    finiteTestFilteredDistanceMeasure μ ν F₁ F₂ ≤ weightedCrossDistanceMeasure μ ν ∧
    weightedCrossDistanceMeasure μ ν univ - finiteTestFilteredDistanceMeasure μ ν F₁ F₂ univ ≤
      ENNReal.ofReal (weightedFilterMassError θ K N) ∧
    Summable (weightedFilterMassError θ K) := by
  have hE : 0 < tolerance θ N * N := by linarith [hpar.2.2.1.1]
  obtain ⟨hdom, hloss⟩ := filteredCrossDistanceMeasure_directional_mass_loss μ ν
    hS₁ hS₂ hμ hν hsep F₁.carrier_measurable F₂.carrier_measurable hdef₁ hdef₂
    F₁.badDirections_measurable F₂.badDirections_measurable F₁.badDirections_symmetric
    F₁.symbol_measurable F₂.symbol_measurable F₁.symbol_range F₂.symbol_range
    (fun _ hx _ hw ↦ F₁.symbol_passing hx hw) (fun _ hy _ hw ↦ F₂.symbol_passing hy hw)
    N hE hpar.filter_log_budget hpin₁ hpin₂
    (fun x _ ↦ F₁.badDirections_short x) (fun y _ ↦ F₂.badDirections_short y)
  refine ⟨hdom, ?_, summable_weightedFilterMassError θ K hθ⟩
  rw [weightedFilterMassError_ofReal θ hK N]
  exact hloss

end FalconerThetaGauge
