module

public import FalconerThetaGauge.DistanceLinearizationGroupCarriers

/-! # Exact scalar group estimates for the actual linearization recurrence -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Classical

namespace FalconerThetaGauge

open GaugeFrostman

theorem linearization_group_neighbor_degree_le_nine {ι : Type*} [Fintype ι]
    (index : ι → ℤ) (hinj : Function.Injective index) (i : ι) :
    (((Finset.univ : Finset ι).filter (fun j ↦ |index i - index j| ≤ 4)).card : ℝ) ≤ 9 := by
  let J := (Finset.univ : Finset ι).filter (fun j ↦ |index i - index j| ≤ 4)
  have hsub : J.image index ⊆ Finset.Icc (index i - 4) (index i + 4) := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    have hj' := abs_le.mp (Finset.mem_filter.mp hj).2
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have h := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective J hinj, Int.card_Icc] at h
  have heq : index i + 4 + 1 - (index i - 4) = (9 : ℤ) := by ring
  rw [heq] at h
  exact_mod_cast h

/-- Nine neighbors and the literal bin-square bound give `108 B ∑ W_G²`
when `C=4B`; no bound is assumed for the actual group collisions. -/
theorem scalarCollisionMass_sum_groups_le {ι : Type*} [Fintype ι]
    (η : ι → Measure ℝ) [∀ i, SFinite (η i)] {p t : ℕ} (hpt : p < t)
    (index : ι → ℤ) (hinj : Function.Injective index)
    (hcarried : ∀ i, ∀ᵐ s ∂η i, s ∈ linearizationDistanceGroupInterval p (index i))
    {C : ℝ} (hC : 0 ≤ C) (m : ι → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hbins : ∀ i, scalarBinSquareMass (η i) (dyadicRadius t) ≤
      ENNReal.ofReal C * ENNReal.ofReal (m i) ^ (2 : ℕ)) :
    scalarCollisionMass (Measure.sum η) (Measure.sum η) (dyadicRadius t) 0 ≤
      ENNReal.ofReal (27 * C * ∑ i, m i ^ (2 : ℕ)) := by
  have hsym : ∀ ⦃i j⦄, |index i - index j| ≤ 4 → |index j - index i| ≤ 4 := by
    intro i j hij
    simpa only [abs_sub_comm] using hij
  have h := scalarCollisionMass_sum_le_graph η (dyadicRadius_pos t)
    (fun i j ↦ |index i - index j| ≤ 4) hsym hC m hm
    (linearization_group_neighbor_degree_le_nine index hinj) hbins
    (fun i j hij ↦ scalarCollisionMass_groups_eq_zero (η i) (η j) hpt
      (hcarried i) (hcarried j) hij)
  convert h using 1
  congr 1
  ring

theorem sum_linearization_group_mass_sq_le_collision {ι : Type*} [Fintype ι]
    (η : ι → Measure ℝ) [∀ i, SFinite (η i)] {p : ℕ} (index : ι → ℤ)
    (hcarried : ∀ i, ∀ᵐ s ∂η i, s ∈ linearizationDistanceGroupInterval p (index i)) :
    (∑ i, (η i univ) ^ (2 : ℕ)) ≤
      scalarCollisionMass (Measure.sum η) (Measure.sum η) (4 * dyadicRadius p) 0 := by
  rw [scalarCollisionMass_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [← scalarCollisionMass_group_self_eq_mass_sq (η i) (hcarried i)]
  exact Finset.single_le_sum (fun j _ ↦
    show (0 : ℝ≥0∞) ≤ scalarCollisionMass (η i) (η j) (4 * dyadicRadius p) 0 from bot_le) hi

/-- The exact coarse-scale comparison contributes the source's factor nine. -/
theorem sum_linearization_group_mass_sq_le_nine_collision {ι : Type*} [Fintype ι]
    (η : ι → Measure ℝ) [∀ i, IsFiniteMeasure (η i)] {p : ℕ} (index : ι → ℤ)
    (hcarried : ∀ i, ∀ᵐ s ∂η i, s ∈ linearizationDistanceGroupInterval p (index i)) :
    (∑ i, (η i univ) ^ (2 : ℕ)) ≤
      9 * scalarCollisionMass (Measure.sum η) (Measure.sum η) (dyadicRadius p) 0 := by
  have h := (sum_linearization_group_mass_sq_le_collision η index hcarried).trans
    (scalarCollisionMass_dilate_le (Measure.sum η) (dyadicRadius_pos p) 4)
  norm_num at h
  simpa only [Measure.sum_fintype] using h

end FalconerThetaGauge
