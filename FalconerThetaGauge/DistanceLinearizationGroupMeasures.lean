module

public import FalconerThetaGauge.DistanceLinearizationBinning

/-! # Literal finite group measures and their bin-square estimates -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Classical

namespace FalconerThetaGauge

theorem scalarCollisionMass_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (η : ι → Measure ℝ) (ζ : κ → Measure ℝ) [∀ i, SFinite (η i)] [∀ j, SFinite (ζ j)]
    (h u : ℝ) :
    scalarCollisionMass (Measure.sum η) (Measure.sum ζ) h u =
      ∑ i, ∑ j, scalarCollisionMass (η i) (ζ j) h u := by
  unfold scalarCollisionMass
  rw [Measure.prod_sum, Measure.sum_apply _ (measurableSet_scalarCollision h u)]
  simp only [tsum_fintype, Fintype.sum_prod_type]

theorem scalarBinSquareMass_sum_le {ι : Type*} [Fintype ι] (η : ι → Measure ℝ) (h : ℝ) :
    scalarBinSquareMass (Measure.sum η) h ≤
      (∑ i, scalarBinSquareMass (η i) h ^ (1 / 2 : ℝ)) ^ (2 : ℕ) := by
  simpa only [Measure.sum_fintype] using scalarBinSquareMass_finsetSum_le Finset.univ η h

theorem scalarBinSquareMass_sum_le_of_component_collision {ι : Type*} [Fintype ι]
    (η : ι → Measure ℝ) [∀ i, SFinite (η i)] {h : ℝ} (hh : 0 < h)
    (C : ℝ≥0∞) (m : ι → ℝ≥0∞)
    (hC : ∀ i, scalarCollisionMass (η i) (η i) h 0 ≤ C * m i ^ (2 : ℕ)) :
    scalarBinSquareMass (Measure.sum η) h ≤ C * (∑ i, m i) ^ (2 : ℕ) := by
  have hcomponent (i : ι) :
      scalarBinSquareMass (η i) h ^ (1 / 2 : ℝ) ≤ C ^ (1 / 2 : ℝ) * m i := by
    have h := ENNReal.rpow_le_rpow ((scalarBinSquareMass_le_collision (η i) hh).trans
      (hC i)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ← ENNReal.rpow_two, ← ENNReal.rpow_mul] at h
    norm_num at h
    exact h
  calc
    _ ≤ (∑ i, scalarBinSquareMass (η i) h ^ (1 / 2 : ℝ)) ^ (2 : ℕ) :=
      scalarBinSquareMass_sum_le η h
    _ ≤ (∑ i, C ^ (1 / 2 : ℝ) * m i) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (by positivity) (Finset.sum_le_sum fun i _ ↦ hcomponent i) 2
    _ = _ := by
      rw [← Finset.mul_sum, mul_pow, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
      norm_num

end FalconerThetaGauge
