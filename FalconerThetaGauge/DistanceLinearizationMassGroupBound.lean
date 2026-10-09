module

public import FalconerThetaGauge.DistanceLinearizationMassGroups

/-! # Actual finite regrouping yields the source fine-to-coarse collision estimate -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal Classical

namespace FalconerThetaGauge

open GaugeFrostman

/-- Genuine cellwise coincidences, true carriers and finite regrouping give `243C`;
the source one-cell constant `C=4B` therefore gives `972B`. -/
theorem scalarCollisionMass_sum_toReal_le_group_bound {ι : Type*} [Fintype ι]
    (η : ι → Measure ℝ) [∀ i, IsFiniteMeasure (η i)] {p t : ℕ} (hpt : p < t)
    (index : ι → ℤ)
    (hcarried : ∀ i, ∀ᵐ s ∂η i, s ∈ linearizationDistanceGroupInterval p (index i))
    {C : ℝ} (hC : 0 ≤ C)
    (hcell : ∀ i, scalarCollisionMass (η i) (η i) (dyadicRadius t) 0 ≤
      ENNReal.ofReal C * (η i univ) ^ (2 : ℕ)) :
    (scalarCollisionMass (Measure.sum η) (Measure.sum η) (dyadicRadius t) 0).toReal ≤
      243 * C * (scalarCollisionMass (Measure.sum η) (Measure.sum η)
        (dyadicRadius p) 0).toReal := by
  let ζ := finiteScalarGroupMeasure η index
  let m : finiteScalarGroupIndices index → ℝ := fun g ↦ (ζ g).real univ
  have hm (g : finiteScalarGroupIndices index) : 0 ≤ m g := measureReal_nonneg
  have hζ (g : finiteScalarGroupIndices index) :
      ∀ᵐ s ∂ζ g, s ∈ linearizationDistanceGroupInterval p (g : ℤ) :=
    ae_finiteScalarGroupMeasure_interval η index p hcarried g
  have hbins (g : finiteScalarGroupIndices index) :
      scalarBinSquareMass (ζ g) (dyadicRadius t) ≤
        ENNReal.ofReal C * ENNReal.ofReal (m g) ^ (2 : ℕ) := by
    have h := scalarBinSquareMass_sum_le_of_component_collision
      (fun i : finiteScalarGroupFiber index g ↦ η i.1) (dyadicRadius_pos t)
      (ENNReal.ofReal C) (fun i ↦ η i.1 univ) (fun i ↦ hcell i.1)
    have heq : (∑ i : finiteScalarGroupFiber index g, η i.1 univ) = ζ g univ := by
      change _ = (Measure.sum fun i : finiteScalarGroupFiber index g ↦ η i.1) univ
      rw [Measure.sum_apply _ MeasurableSet.univ, tsum_fintype]
    change scalarBinSquareMass (ζ g) (dyadicRadius t) ≤
      ENNReal.ofReal C * (∑ i : finiteScalarGroupFiber index g, η i.1 univ) ^ (2 : ℕ) at h
    rw [heq] at h
    simpa only [m, Measure.real, ENNReal.ofReal_toReal (measure_ne_top (ζ g) univ)] using h
  have hgraph := scalarCollisionMass_sum_groups_le ζ hpt
    (fun g ↦ (g : ℤ)) Subtype.val_injective hζ hC m hm hbins
  have hsum := sum_linearization_group_mass_sq_le_nine_collision ζ
    (fun g ↦ (g : ℤ)) hζ
  have hreal := ENNReal.toReal_mono (by unfold scalarCollisionMass; finiteness) hsum
  have hreal' : (∑ g, m g ^ (2 : ℕ)) ≤
      9 * (scalarCollisionMass (Measure.sum ζ) (Measure.sum ζ) (dyadicRadius p) 0).toReal := by
    have hfinite : ∀ g ∈ (Finset.univ : Finset (finiteScalarGroupIndices index)),
        (ζ g univ) ^ (2 : ℕ) ≠ ∞ := fun g _ ↦ by finiteness
    simpa only [ENNReal.toReal_sum hfinite, ENNReal.toReal_pow,
      ENNReal.toReal_mul, ENNReal.toReal_ofNat, m, Measure.real] using hreal
  have hfine := ENNReal.toReal_mono (by finiteness) hgraph
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 27 * C * ∑ g, m g ^ (2 : ℕ))] at hfine
  have hbound := hfine.trans (mul_le_mul_of_nonneg_left hreal' (by positivity : 0 ≤ 27 * C))
  rw [sum_finiteScalarGroupMeasures] at hbound
  convert hbound using 1
  ring

end FalconerThetaGauge
