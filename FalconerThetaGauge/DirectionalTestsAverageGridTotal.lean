module

public import FalconerThetaGauge.DirectionalTestsAverageGridCount

/-! # The genuine total occupied-grid count for the coarsest tube shells -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- Regularity and total probability bound the actual number of occupied cells. -/
theorem occupiedUnitCells_count_mul_max_le (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    {ε : ℝ} {N p : ℕ} (hreg : IsRegularThrough ε N ρ) (hp : p ≤ N) :
    ((occupiedUnitCells ρ p).card : ℝ) * maxCellMass ρ p ≤ (2 : ℝ) ^ (ε * N) := by
  obtain ⟨kmax, _, hmax⟩ := exists_unitCellWeight_eq_maxCellMass ρ p
  calc
    _ = ∑ _k ∈ occupiedUnitCells ρ p, maxCellMass ρ p := by simp
    _ ≤ ∑ k ∈ occupiedUnitCells ρ p, (2 : ℝ) ^ (ε * N) * unitCellWeight ρ p k := by
      apply Finset.sum_le_sum
      intro k hk
      rw [hmax]
      exact hreg p hp kmax k (Finset.mem_filter.mp hk).2
    _ = (2 : ℝ) ^ (ε * N) * ∑ k ∈ occupiedUnitCells ρ p, unitCellWeight ρ p k :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
      simpa only [occupiedUnitCells, mul_one] using mul_le_mul_of_nonneg_left
        (sum_unitCellWeight_subfamily_le_one ρ p _ (Finset.filter_subset _ _))
        (Real.rpow_nonneg (by norm_num) (ε * N))

/-- The actual occupied-grid count in the source's excess-function normalization. -/
theorem occupiedUnitCells_count_le_excess (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {ε : ℝ} {N p : ℕ} (hN : 0 < N)
    (hreg : IsRegularThrough ε N ρ) (hp : p ≤ N) :
    ((occupiedUnitCells ρ p).card : ℝ) ≤ (2 : ℝ) ^ (ε * N) * (2 : ℝ) ^ (p : ℝ) *
      (2 : ℝ) ^ ((N : ℝ) * (regularMeasureExcess ρ N p - regularMeasureExcess ρ N 0)) := by
  have hcount := (le_div_iff₀ (maxCellMass_pos ρ hρ p)).mpr
    (occupiedUnitCells_count_mul_max_le ρ hreg hp)
  have hzero : regularMeasureExcess ρ N 0 = 0 := by
    simp [regularMeasureExcess, maxCellMass_zero ρ hρ]
  convert hcount using 1
  rw [hzero, maxCellMass_eq_power_excess ρ hρ hN p]
  simp only [sub_zero, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

end FalconerThetaGauge
