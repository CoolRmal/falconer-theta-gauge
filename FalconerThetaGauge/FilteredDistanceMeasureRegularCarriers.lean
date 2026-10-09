module

public import FalconerThetaGauge.FilteredDistanceMeasureFiniteTests
public import FalconerThetaGauge.RegularDecompositionMeasures

/-!
# The actual regular-decomposition carriers in the filter

The discarded source mass is supplied by the proved dyadic decomposition,
including its rounded parameters and original half-open cell carriers.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace FalconerThetaGauge

open GaugeSeparatedMeasures

/-- The actual union of all retained regular-piece carriers at terminal scale `N`. -/
def regularFilterCarrier (μ : Measure Plane) (θ : ℝ) (N : ℕ) : Set Plane :=
  ⋃ t ∈ regularDyadicKeptTypes μ (tolerance θ N) (blockParameter θ N) N,
    regularDyadicPartCarrier μ (tolerance θ N) N t

theorem measurableSet_regularFilterCarrier (μ : Measure Plane) (θ : ℝ) (N : ℕ) :
    MeasurableSet (regularFilterCarrier μ θ N) :=
  MeasurableSet.biUnion (Finset.countable_toSet _) (fun t _ ↦
    measurableSet_regularDyadicPartCarrier μ (tolerance θ N) N t)

/-- The actual parameter facts imply all hypotheses of the discarded-mass estimate. -/
theorem ParameterFacts.regular_filter_parameters {θ : ℝ} {N : ℕ} (h : ParameterFacts θ N) :
    0 < tolerance θ N ∧ tolerance θ N ≤ 1 ∧ blockParameter θ N ≤ 4 := by
  have hN : 0 < N := lt_of_lt_of_le (by norm_num) h.1
  have hk := blockParameter_pos θ hN
  rcases h.2.2.2.2 with ⟨_, hkg, hgsmall, _, htol, _, _, _⟩
  have hkone : blockParameter θ N ≤ 1 := by linarith
  have hksq : blockParameter θ N ^ 2 ≤ 1 := by nlinarith
  exact ⟨tolerance_pos θ hN, by linarith, by linarith⟩

/-- The actual complement of the retained carrier has the `2 R^(-κ/4)` mass bound. -/
theorem regularFilterCarrier_compl_mass_le (μ : Measure Plane) [IsProbabilityMeasure μ]
    {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) (hμ : μ unitSquare = 1) :
    μ (regularFilterCarrier μ θ N)ᶜ ≤
      ENNReal.ofReal (2 * (2 : ℝ) ^ (-(blockParameter θ N * N) / 4)) := by
  obtain ⟨hε, hε₁, hκ⟩ := hpar.regular_filter_parameters
  have hdiscard := regularDyadicPartCarrier_discarded_mass_le μ hε hε₁ hκ
    hpar.2.2.1.1 hpar.2.2.1.2
  have hsq : MeasurableSet unitSquare := by
    simp only [unitSquare, ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_Ico.preimage (by fun_prop)
  have hcarrier : ∀ᵐ x ∂μ, x ∈ unitSquare :=
    (ae_mem_iff_measure_eq hsq.nullMeasurableSet).2 (by simpa using hμ)
  have heq : μ (regularFilterCarrier μ θ N)ᶜ =
      μ (unitSquare \ regularFilterCarrier μ θ N) := by
    apply measure_congr
    filter_upwards [hcarrier] with x hx
    apply propext
    simp [hx]
  calc
    μ (regularFilterCarrier μ θ N)ᶜ = μ (unitSquare \ regularFilterCarrier μ θ N) := heq
    _ = ENNReal.ofReal (μ.real (unitSquare \ regularFilterCarrier μ θ N)) :=
      (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    _ ≤ ENNReal.ofReal (2 * (2 : ℝ) ^ (-(blockParameter θ N * N) / 4)) := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [regularFilterCarrier, neg_div] using hdiscard

/-- Lemma 6.13 with actual regular-decomposition carriers: the discarded mass
is proved from the decomposition, while the masks retain their concrete test data. -/
theorem finiteTestFilteredDistanceMeasure_regular_mass_loss
    (μ ν : Measure Plane) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {θ K : ℝ} (hθ : 2 / 3 < θ) (hK : 0 ≤ K) {N : ℕ} (hpar : ParameterFacts θ N)
    (hunit₁ : μ unitSquare = 1) (hunit₂ : ν unitSquare = 1)
    {S₁ S₂ : Set Plane} (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂)
    (hμ : μ S₁ = 1) (hν : ν S₂ = 1)
    (hsep : ∀ x ∈ S₁, ∀ y ∈ S₂, (24 / 100 : ℝ) ≤ dist x y)
    (F₁ F₂ : FiniteDirectionalFilter N (tolerance θ N * N))
    (hC₁ : F₁.carrier = regularFilterCarrier μ θ N)
    (hC₂ : F₂.carrier = regularFilterCarrier ν θ N)
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
  apply finiteTestFilteredDistanceMeasure_mass_loss μ ν hθ hK hpar hS₁ hS₂ hμ hν hsep
    F₁ F₂ _ _ hpin₁ hpin₂
  · rw [hC₁]
    exact regularFilterCarrier_compl_mass_le μ hpar hunit₁
  · rw [hC₂]
    exact regularFilterCarrier_compl_mass_le ν hpar hunit₂

end FalconerThetaGauge
