module

public import FalconerThetaGauge.FilteredDistanceMeasureDirections

/-!
# Mass loss for actual directional masks

The four excluded sets are the two regular-carrier complements and the two
actual bad-direction pair sets. Symmetry is used only for the first pin,
where the manuscript's direction is the antipode of the outgoing radial map.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace FalconerThetaGauge

/-- The actual union on which the two directional masks may remove mass. -/
def filterExcludedPairs (C₁ C₂ : Set Plane) (Z₁ Z₂ : Set (Plane × UnitCircle)) :
    Set (Plane × Plane) :=
  ((C₁ᶜ ×ˢ univ) ∪ (univ ×ˢ C₂ᶜ)) ∪ leftBadPairs Z₁ ∪ rightBadPairs Z₂

theorem measurableSet_filterExcludedPairs {C₁ C₂ : Set Plane}
    (hC₁ : MeasurableSet C₁) (hC₂ : MeasurableSet C₂)
    {Z₁ Z₂ : Set (Plane × UnitCircle)} (hZ₁ : MeasurableSet Z₁)
    (hZ₂ : MeasurableSet Z₂) : MeasurableSet (filterExcludedPairs C₁ C₂ Z₁ Z₂) :=
  ((hC₁.compl.prod MeasurableSet.univ).union (MeasurableSet.univ.prod hC₂.compl)).union
    (measurableSet_leftBadPairs hZ₁) |>.union (measurableSet_rightBadPairs hZ₂)

/-- The source's level-zero masks equal one off the actual excluded pairs. -/
theorem directionalPairMask_eq_one_off_filterExcludedPairs
    {C₁ C₂ : Set Plane} {Z₁ Z₂ : Set (Plane × UnitCircle)}
    {b₁ b₂ : Plane → UnitCircle → ℝ}
    (h₁ : ∀ x ∈ C₁, ∀ w, (x, w) ∉ Z₁ → b₁ x w = 1)
    (h₂ : ∀ y ∈ C₂, ∀ w, (y, w) ∉ Z₂ → b₂ y w = 1)
    {p : Plane × Plane} (hp : p ∉ filterExcludedPairs C₁ C₂ Z₁ Z₂) :
    directionalPairMask b₁ b₂ p = 1 := by
  have hx : p.1 ∈ C₁ := by
    by_contra hx
    exact hp (Or.inl (Or.inl (Or.inl ⟨hx, mem_univ _⟩)))
  have hy : p.2 ∈ C₂ := by
    by_contra hy
    exact hp (Or.inl (Or.inl (Or.inr ⟨mem_univ _, hy⟩)))
  have hz₁ : (p.1, pairDirection p.1 p.2) ∉ Z₁ := fun hz ↦
    hp (Or.inl (Or.inr hz))
  have hz₂ : (p.2, pairDirection p.1 p.2) ∉ Z₂ := fun hz ↦ hp (Or.inr hz)
  simp [directionalPairMask, h₁ _ hx _ hz₁, h₂ _ hy _ hz₂]

/-- The union bound retains both actual carrier defects and both actual radial costs. -/
theorem measure_filterExcludedPairs_le (μ ν : Measure Plane)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {C₁ C₂ : Set Plane} {Z₁ Z₂ : Set (Plane × UnitCircle)}
    {δ₁ δ₂ D₁ D₂ : ℝ≥0∞} (hC₁ : μ C₁ᶜ ≤ δ₁) (hC₂ : ν C₂ᶜ ≤ δ₂)
    (hZ₁ : μ.prod ν (leftBadPairs Z₁) ≤ D₁)
    (hZ₂ : μ.prod ν (rightBadPairs Z₂) ≤ D₂) :
    μ.prod ν (filterExcludedPairs C₁ C₂ Z₁ Z₂) ≤ δ₁ + δ₂ + D₁ + D₂ := by
  calc
    μ.prod ν (filterExcludedPairs C₁ C₂ Z₁ Z₂) ≤
        μ.prod ν ((C₁ᶜ ×ˢ univ) ∪ (univ ×ˢ C₂ᶜ)) +
          μ.prod ν (leftBadPairs Z₁) + μ.prod ν (rightBadPairs Z₂) :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ δ₁ + δ₂ + D₁ + D₂ := by
      have hC : μ.prod ν ((C₁ᶜ ×ˢ univ) ∪ (univ ×ˢ C₂ᶜ)) ≤ δ₁ + δ₂ := by
        calc
          _ ≤ μ.prod ν (C₁ᶜ ×ˢ univ) + μ.prod ν (univ ×ˢ C₂ᶜ) := measure_union_le _ _
          _ = μ C₁ᶜ + ν C₂ᶜ := by simp
          _ ≤ δ₁ + δ₂ := add_le_add hC₁ hC₂
      exact add_le_add (add_le_add hC hZ₁) hZ₂

/-- Definition 6.12 and the quantitative part of Lemma 6.13, for actual Borel masks,
actual symmetric bad-direction families, and actual prepared radial densities. -/
theorem filteredCrossDistanceMeasure_directional_mass_loss
    (μ ν : Measure Plane) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {S₁ S₂ C₁ C₂ : Set Plane}
    (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂)
    (hμ : μ S₁ = 1) (hν : ν S₂ = 1)
    (hsep : ∀ x ∈ S₁, ∀ y ∈ S₂, (24 / 100 : ℝ) ≤ dist x y)
    (hC₁ : MeasurableSet C₁) (hC₂ : MeasurableSet C₂)
    {δ₁ δ₂ : ℝ≥0∞} (hdef₁ : μ C₁ᶜ ≤ δ₁) (hdef₂ : ν C₂ᶜ ≤ δ₂)
    {Z₁ Z₂ : Set (Plane × UnitCircle)} (hZ₁ : MeasurableSet Z₁) (hZ₂ : MeasurableSet Z₂)
    (hsym₁ : IsSymmetricBadDirections Z₁)
    {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (Function.uncurry b₁)) (hb₂ : Measurable (Function.uncurry b₂))
    (hrange₁ : ∀ x w, b₁ x w ∈ Icc 0 1) (hrange₂ : ∀ x w, b₂ x w ∈ Icc 0 1)
    (hgood₁ : ∀ x ∈ C₁, ∀ w, (x, w) ∉ Z₁ → b₁ x w = 1)
    (hgood₂ : ∀ y ∈ C₂, ∀ w, (y, w) ∉ Z₂ → b₂ y w = 1)
    (N : ℕ) {E : ℝ} (hE : 0 < E)
    (hbudget : Real.log (2 * Real.pi * ((N : ℝ) ^ 2 + 1)) ≤
      (2 * Real.log 2 - 1) * E) {K : ℝ≥0∞}
    (hpin₁ : ∀ x ∈ S₁,
      circleArcLength.withDensity (radialProjectionDensity ν x) = ν.map (radialProjection x) ∧
      radialOrliczMoment ν 8 x ≤ K)
    (hpin₂ : ∀ y ∈ S₂,
      circleArcLength.withDensity (radialProjectionDensity μ y) = μ.map (radialProjection y) ∧
      radialOrliczMoment μ 8 y ≤ K)
    (hlength₁ : ∀ x ∈ S₁,
      circleArcLength (badDirectionsAt Z₁ x) ≤ ENNReal.ofReal (filterBadDirectionLength N E))
    (hlength₂ : ∀ y ∈ S₂,
      circleArcLength (badDirectionsAt Z₂ y) ≤ ENNReal.ofReal (filterBadDirectionLength N E)) :
    filteredCrossDistanceMeasure μ ν (directionalPairMask b₁ b₂) ≤
      weightedCrossDistanceMeasure μ ν ∧
    weightedCrossDistanceMeasure μ ν univ -
        filteredCrossDistanceMeasure μ ν (directionalPairMask b₁ b₂) univ ≤
      ENNReal.ofReal (21 / 10) * (δ₁ + δ₂ + 2 * radialFilterCost N E K) := by
  have hc := ae_product_carriers μ ν hS₁ hS₂ hμ hν
  have hne : ∀ᵐ p ∂μ.prod ν, p.1 ≠ p.2 := by
    filter_upwards [hc] with p hp
    exact dist_pos.mp (lt_of_lt_of_le (by norm_num) (hsep p.1 hp.1 p.2 hp.2))
  have hleft : μ.prod ν (leftBadPairs Z₁) ≤ radialFilterCost N E K := by
    rw [measure_leftBadPairs_eq_radialBadPairs μ ν hsym₁ hne]
    exact measure_radialBadPairs_le_filterCost μ ν hS₁ hμ hZ₁ N hE hbudget hpin₁ hlength₁
  have hright : μ.prod ν (rightBadPairs Z₂) ≤ radialFilterCost N E K := by
    rw [measure_rightBadPairs μ ν hZ₂]
    exact measure_radialBadPairs_le_filterCost ν μ hS₂ hν hZ₂ N hE hbudget hpin₂ hlength₂
  constructor
  · exact filteredCrossDistanceMeasure_le μ ν (ae_of_all _ fun p ↦
      (directionalPairMask_mem_Icc hrange₁ hrange₂ p).2)
  · calc
      _ ≤ ENNReal.ofReal (21 / 10) * μ.prod ν (filterExcludedPairs C₁ C₂ Z₁ Z₂) := by
        apply filteredCrossDistanceMeasure_mass_loss_le μ ν
          (measurable_directionalPairMask hb₁ hb₂)
          (measurableSet_filterExcludedPairs hC₁ hC₂ hZ₁ hZ₂)
        · filter_upwards [hc] with p hp
          exact crossDistanceWeight_le_two_point_one (hsep p.1 hp.1 p.2 hp.2)
        · exact ae_of_all _ fun p hp ↦
            directionalPairMask_eq_one_off_filterExcludedPairs hgood₁ hgood₂ hp
      _ ≤ ENNReal.ofReal (21 / 10) * (δ₁ + δ₂ +
          radialFilterCost N E K + radialFilterCost N E K) :=
        mul_le_mul' le_rfl (measure_filterExcludedPairs_le μ ν hdef₁ hdef₂ hleft hright)
      _ = ENNReal.ofReal (21 / 10) * (δ₁ + δ₂ + 2 * radialFilterCost N E K) := by
        rw [two_mul, ← add_assoc]

end FalconerThetaGauge
