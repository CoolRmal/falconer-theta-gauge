/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureExcessGauge
public import FalconerThetaGauge.RegularDecompositionMeasures

/-!
# Actual excess properties and occupied-cell counts of retained parts

The normalized retained carriers satisfy Lemma 5.10, and their occupied
descendants satisfy the counting estimate (5.2).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem measurableSet_unitSquare : MeasurableSet unitSquare := by
  rw [← biUnion_unitCellIndices 0]
  exact measurableSet_cellUnion 0 _

/-- A cell outside the unit square is null for a probability carried by that square. -/
theorem unitCellWeight_eq_zero_of_not_mem (μ : Measure Plane) [IsProbabilityMeasure μ]
    (hμ : μ unitSquare = 1) (n : ℕ) {k : Fin 2 → ℤ} (hk : k ∉ unitCellIndices n) :
    unitCellWeight μ n k = 0 := by
  have hdisjoint := dyadicCube_disjoint_cellUnion_of_not_mem n hk
  have hcarrier : cellUnion n (unitCellIndices n) = unitSquare := biUnion_unitCellIndices n
  rw [hcarrier] at hdisjoint
  have hsub : dyadicCube n k ⊆ unitSquareᶜ := by
    intro x hx hxU
    exact Set.disjoint_left.mp hdisjoint hx hxU
  have hnull : μ unitSquareᶜ = 0 := by
    rw [measure_compl measurableSet_unitSquare (measure_ne_top μ _), measure_univ, hμ,
      tsub_self]
  rw [unitCellWeight, Measure.real, measure_mono_null hsub hnull, ENNReal.toReal_zero]

/-- The actual maximum also bounds every cell indexed outside the finite unit grid. -/
theorem unitCellWeight_le_maxCellMass_all (μ : Measure Plane) [IsProbabilityMeasure μ]
    (hμ : μ unitSquare = 1) (n : ℕ) (k : Fin 2 → ℤ) :
    unitCellWeight μ n k ≤ maxCellMass μ n := by
  by_cases hk : k ∈ unitCellIndices n
  · exact unitCellWeight_le_maxCellMass μ n hk
  · rw [unitCellWeight_eq_zero_of_not_mem μ hμ n hk]
    exact maxCellMass_nonneg μ n

/-- The actual occupied generation-`p` descendants of one generation-`g` cell. -/
def occupiedCellDescendants (ρ : Measure Plane) (g p : ℕ) (q : Fin 2 → ℤ) :
    Finset (Fin 2 → ℤ) :=
  (unitCellIndices p).filter
    (fun k ↦ ancestor (p - g) k = q ∧ 0 < unitCellWeight ρ p k)

/-- Finite additivity bounds the total actual descendant mass by the parent mass. -/
theorem sum_occupiedCellDescendants_le (ρ : Measure Plane) [IsFiniteMeasure ρ]
    {g p : ℕ} (hgp : g ≤ p) (q : Fin 2 → ℤ) :
    (∑ k ∈ occupiedCellDescendants ρ g p q, unitCellWeight ρ p k) ≤
      unitCellWeight ρ g q := by
  have hsub : occupiedCellDescendants ρ g p q ⊆
      (unitCellIndices p).filter (fun k ↦ ancestor (p - g) k = q) := by
    intro k hk
    obtain ⟨hkU, hancestor, _⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr ⟨hkU, hancestor⟩
  calc
    _ ≤ ∑ k ∈ (unitCellIndices p).filter (fun k ↦ ancestor (p - g) k = q),
        unitCellWeight ρ p k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ ↦ unitCellWeight_nonneg ρ p k)
    _ = (ρ.restrict (cellUnion p (unitCellIndices p))).real (dyadicCube g q) :=
      (real_restrict_cellUnion_dyadicCube ρ hgp _ _).symm
    _ ≤ _ := by
      unfold unitCellWeight Measure.real
      rw [Measure.restrict_apply (measurableSet_dyadicCube g q)]
      exact ENNReal.toReal_mono (measure_ne_top ρ _) (measure_mono inter_subset_left)

/-- Regularity and the actual finite mass sum give the occupied descendant count. -/
theorem occupiedCellDescendants_count_mul_max_le (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {ε : ℝ} {N g p : ℕ}
    (hreg : IsRegularThrough ε N ρ) (hgp : g ≤ p) (hp : p ≤ N) (q : Fin 2 → ℤ) :
    ((occupiedCellDescendants ρ g p q).card : ℝ) * maxCellMass ρ p ≤
      (2 : ℝ) ^ (ε * N) * maxCellMass ρ g := by
  obtain ⟨kmax, _, hmax⟩ := exists_unitCellWeight_eq_maxCellMass ρ p
  have hsum : ((occupiedCellDescendants ρ g p q).card : ℝ) * maxCellMass ρ p ≤
      (2 : ℝ) ^ (ε * N) *
        ∑ k ∈ occupiedCellDescendants ρ g p q, unitCellWeight ρ p k := by
    calc
      _ = ∑ _k ∈ occupiedCellDescendants ρ g p q, maxCellMass ρ p := by simp
      _ ≤ ∑ k ∈ occupiedCellDescendants ρ g p q,
          (2 : ℝ) ^ (ε * N) * unitCellWeight ρ p k := by
        apply Finset.sum_le_sum
        intro k hk
        rw [hmax]
        exact hreg p hp kmax k (Finset.mem_filter.mp hk).2.2
      _ = _ := (Finset.mul_sum _ _ _).symm
  exact hsum.trans (mul_le_mul_of_nonneg_left
    ((sum_occupiedCellDescendants_le ρ hgp q).trans
      (unitCellWeight_le_maxCellMass_all ρ hρ g q)) (Real.rpow_nonneg (by norm_num) _))

/-- The literal occupied-descendant estimate (5.2) in terms of the actual excess function. -/
theorem occupiedCellDescendants_count_le (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {ε : ℝ} {N g p : ℕ} (hN : 0 < N)
    (hreg : IsRegularThrough ε N ρ) (hgp : g ≤ p) (hp : p ≤ N) (q : Fin 2 → ℤ) :
    ((occupiedCellDescendants ρ g p q).card : ℝ) ≤ (2 : ℝ) ^ (ε * N) *
      (2 : ℝ) ^ ((p : ℝ) - g) *
        (2 : ℝ) ^ ((N : ℝ) * (regularMeasureExcess ρ N p - regularMeasureExcess ρ N g)) := by
  have hcount := (le_div_iff₀ (maxCellMass_pos ρ hρ p)).mpr
    (occupiedCellDescendants_count_mul_max_le ρ hρ hreg hgp hp q)
  convert hcount using 1
  rw [maxCellMass_eq_power_excess ρ hρ hN g, maxCellMass_eq_power_excess ρ hρ hN p]
  simp only [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- Lemma 5.10 for each actual type carrier retained in the constructed decomposition. -/
theorem regularDyadicPartMeasure_excess_properties
    (μ : Measure Plane) [IsProbabilityMeasure μ] {θ C ε κ : ℝ}
    (hθ : 0 < θ) (hC : 0 < C) (hκ : 0 ≤ κ) (hball : HasGaugeBallBound μ θ C)
    {N : ℕ} (hN : 0 < N) (hconstant : Real.log C / Real.log 2 ≤ κ * N / 2)
    {t : List ℕ} (ht : t ∈ regularDyadicKeptTypes μ ε κ N) :
    regularMeasureExcess (regularDyadicPartMeasure μ ε N t) N 0 = 0 ∧
      (∀ n m : ℕ, |regularMeasureExcess (regularDyadicPartMeasure μ ε N t) N n -
        regularMeasureExcess (regularDyadicPartMeasure μ ε N t) N m| ≤ |(n : ℝ) - m| / N) ∧
      (∀ n : ℕ, gaugeExcess θ N n - κ ≤
        regularMeasureExcess (regularDyadicPartMeasure μ ε N t) N n) ∧
      (∀ n : ℕ, regularMeasureExcess (regularDyadicPartMeasure μ ε N t) N n ≤ (n : ℝ) / N) := by
  obtain ⟨hprob, hρ⟩ := regularDyadicPartMeasure_probability μ ε κ N ht
  have : IsProbabilityMeasure (normalizedRestrict μ (regularDyadicPartCarrier μ ε N t)) :=
    hprob
  exact regularMeasureExcess_normalizedRestrict_properties μ _ hθ hC hκ hball hN
    (regularDyadicPartCarrier_mass_ge μ ε κ N ht) hconstant hρ

end FalconerThetaGauge
