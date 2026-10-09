module

public import FalconerThetaGauge.FilteredDistanceMeasureRegularCarriers

/-!
# The actual weighted approximants have summable removed mass

This module converts the proved ENNReal loss into the real mass difference
used by the Fourier reconstruction theorem. Its approximants retain the
literal finite mask products and the actual regular carriers at every scale.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerThetaGauge

open GaugeSeparatedMeasures

/-- A finite dominated measure's real mass loss is its true ENNReal mass loss converted to real. -/
theorem real_measure_mass_loss_eq_toReal (α τ : Measure ℝ)
    [IsFiniteMeasure α] [IsFiniteMeasure τ] (hdom : τ ≤ α) :
    α.real univ - τ.real univ = (α univ - τ univ).toReal := by
  exact (ENNReal.toReal_sub_of_le (hdom univ) (measure_ne_top α univ)).symm

/-- Genuine summable ENNReal loss bounds imply summability of the actual real removed masses. -/
theorem summable_real_measure_mass_loss_of_bound (α : Measure ℝ) [IsFiniteMeasure α]
    (τ : ℕ → Measure ℝ) [∀ n, IsFiniteMeasure (τ n)] {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hdom : ∀ n, τ n ≤ α)
    (hloss : ∀ n, α univ - τ n univ ≤ ENNReal.ofReal (a n)) :
    Summable (fun n ↦ α.real univ - (τ n).real univ) := by
  apply Summable.of_nonneg_of_le _ _ hs
  · intro n
    rw [real_measure_mass_loss_eq_toReal α (τ n) (hdom n)]
    exact ENNReal.toReal_nonneg
  · intro n
    rw [real_measure_mass_loss_eq_toReal α (τ n) (hdom n)]
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hloss n)
    simpa only [ENNReal.toReal_ofReal (ha n)] using hreal

/-- The actual terminal-scale filtered measure sequence, allowing omitted initial scales. -/
def finiteTestFilteredDistanceSequence (μ ν : Measure Plane) (θ : ℝ) (N₀ : ℕ)
    (F₁ F₂ : ∀ n : ℕ, FiniteDirectionalFilter (n + N₀)
      (tolerance θ (n + N₀) * ((n + N₀ : ℕ) : ℝ))) : ℕ → Measure ℝ :=
  fun n ↦ finiteTestFilteredDistanceMeasure μ ν (F₁ n) (F₂ n)

/-- The actual Definition 6.12 sequence has finite dominated approximants and
summable removed mass, with defects proved from the actual dyadic decomposition. -/
theorem finiteTestFilteredDistanceSequence_summable_removed_mass
    (μ ν : Measure Plane) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {θ K : ℝ} (hθ : 2 / 3 < θ) (hK : 0 ≤ K) (N₀ : ℕ)
    (hpar : ∀ n : ℕ, ParameterFacts θ (n + N₀))
    (hunit₁ : μ unitSquare = 1) (hunit₂ : ν unitSquare = 1)
    {S₁ S₂ : Set Plane} (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂)
    (hμ : μ S₁ = 1) (hν : ν S₂ = 1)
    (hsep : ∀ x ∈ S₁, ∀ y ∈ S₂, (24 / 100 : ℝ) ≤ dist x y)
    (F₁ F₂ : ∀ n : ℕ, FiniteDirectionalFilter (n + N₀)
      (tolerance θ (n + N₀) * ((n + N₀ : ℕ) : ℝ)))
    (hC₁ : ∀ n, (F₁ n).carrier = regularFilterCarrier μ θ (n + N₀))
    (hC₂ : ∀ n, (F₂ n).carrier = regularFilterCarrier ν θ (n + N₀))
    (hpin₁ : ∀ x ∈ S₁,
      circleArcLength.withDensity (radialProjectionDensity ν x) = ν.map (radialProjection x) ∧
      radialOrliczMoment ν 8 x ≤ ENNReal.ofReal K)
    (hpin₂ : ∀ y ∈ S₂,
      circleArcLength.withDensity (radialProjectionDensity μ y) = μ.map (radialProjection y) ∧
      radialOrliczMoment μ 8 y ≤ ENNReal.ofReal K) :
    IsFiniteMeasure (weightedCrossDistanceMeasure μ ν) ∧
    (∀ n, IsFiniteMeasure (finiteTestFilteredDistanceSequence μ ν θ N₀ F₁ F₂ n)) ∧
    (∀ n, finiteTestFilteredDistanceSequence μ ν θ N₀ F₁ F₂ n ≤
      weightedCrossDistanceMeasure μ ν) ∧
    Summable (fun n ↦ (weightedCrossDistanceMeasure μ ν).real univ -
      (finiteTestFilteredDistanceSequence μ ν θ N₀ F₁ F₂ n).real univ) := by
  have hweight : ∀ᵐ p ∂μ.prod ν, crossDistanceWeight p ≤ ENNReal.ofReal (21 / 10) := by
    filter_upwards [ae_product_carriers μ ν hS₁ hS₂ hμ hν] with p hp
    exact crossDistanceWeight_le_two_point_one (hsep p.1 hp.1 p.2 hp.2)
  have hfinite : IsFiniteMeasure (weightedCrossDistanceMeasure μ ν) :=
    isFiniteMeasure_weightedCrossDistanceMeasure μ ν ENNReal.ofReal_ne_top hweight
  have hscale (n : ℕ) := finiteTestFilteredDistanceMeasure_regular_mass_loss μ ν hθ hK
    (hpar n) hunit₁ hunit₂ hS₁ hS₂ hμ hν hsep (F₁ n) (F₂ n) (hC₁ n) (hC₂ n) hpin₁ hpin₂
  have hdom : ∀ n, finiteTestFilteredDistanceSequence μ ν θ N₀ F₁ F₂ n ≤
      weightedCrossDistanceMeasure μ ν := fun n ↦ (hscale n).1
  have hfilters : ∀ n, IsFiniteMeasure (finiteTestFilteredDistanceSequence μ ν θ N₀ F₁ F₂ n) :=
    fun n ↦ isFiniteMeasure_of_le (weightedCrossDistanceMeasure μ ν) (hdom n)
  refine ⟨hfinite, hfilters, hdom, ?_⟩
  apply summable_real_measure_mass_loss_of_bound _ _
    (fun n ↦ weightedFilterMassError_nonneg hK (n + N₀))
    ((summable_nat_add_iff N₀).2 (summable_weightedFilterMassError θ K hθ)) hdom
  exact fun n ↦ (hscale n).2.1

end FalconerThetaGauge
