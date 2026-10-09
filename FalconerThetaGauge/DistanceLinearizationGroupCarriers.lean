module

public import FalconerThetaGauge.DistanceLinearizationGroupGeometry
public import FalconerThetaGauge.DistanceLinearizationGroupSchur

/-! # Actual carried group measures have sparse collisions and coarse mass-square bounds -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Classical

namespace FalconerThetaGauge

open GaugeFrostman

theorem scalarCollisionMass_eq_zero_of_carriers (η ζ : Measure ℝ) [SFinite ζ]
    {S T : Set ℝ} (hη : ∀ᵐ s ∂η, s ∈ S) (hζ : ∀ᵐ s ∂ζ, s ∈ T)
    {h : ℝ} (hseparated : ∀ s ∈ S, ∀ t ∈ T, ¬|s - t| ≤ h) :
    scalarCollisionMass η ζ h 0 = 0 := by
  apply le_antisymm _ bot_le
  change η.prod ζ {p : ℝ × ℝ | |p.1 - p.2 - 0| ≤ h} ≤ 0
  rw [← measure_empty (μ := η.prod ζ)]
  apply measure_mono_ae
  apply (Measure.ae_prod_iff_ae_ae
    ((measurableSet_scalarCollision h 0).imp MeasurableSet.empty)).mpr
  filter_upwards [hη] with s hs
  filter_upwards [hζ] with t ht
  intro hcollision
  exact False.elim (hseparated s hs t ht (by simpa only [sub_zero] using hcollision))

theorem scalarCollisionMass_self_eq_mass_sq_of_diameter (η : Measure ℝ) [SFinite η]
    {S : Set ℝ} (hη : ∀ᵐ s ∂η, s ∈ S) {h : ℝ}
    (hdiameter : ∀ s ∈ S, ∀ t ∈ S, |s - t| ≤ h) :
    scalarCollisionMass η η h 0 = (η univ) ^ (2 : ℕ) := by
  have hae : ∀ᵐ z ∂η.prod η, z ∈ {p : ℝ × ℝ | |p.1 - p.2 - 0| ≤ h} := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_scalarCollision h 0)).mpr
    filter_upwards [hη] with s hs
    filter_upwards [hη] with t ht
    simpa only [mem_ofPred_eq, sub_zero] using hdiameter s hs t ht
  have heq : {p : ℝ × ℝ | |p.1 - p.2 - 0| ≤ h} =ᵐ[η.prod η] univ := by
    filter_upwards [hae] with z hz
    simp only [eq_iff_iff, mem_univ, iff_true]
    exact hz
  rw [scalarCollisionMass, measure_congr heq, ← univ_prod_univ, Measure.prod_prod, pow_two]

theorem scalarCollisionMass_groups_eq_zero (η ζ : Measure ℝ) [SFinite ζ]
    {p t : ℕ} (hpt : p < t) {k k' : ℤ}
    (hη : ∀ᵐ s ∂η, s ∈ linearizationDistanceGroupInterval p k)
    (hζ : ∀ᵐ s ∂ζ, s ∈ linearizationDistanceGroupInterval p k')
    (hunlinked : ¬|k - k'| ≤ 4) : scalarCollisionMass η ζ (dyadicRadius t) 0 = 0 := by
  exact scalarCollisionMass_eq_zero_of_carriers η ζ hη hζ
    (fun s hs s' hs' hcollision ↦ hunlinked
      (linearization_group_collision_neighbors hpt hs hs' hcollision))

theorem scalarCollisionMass_group_self_eq_mass_sq (η : Measure ℝ) [SFinite η]
    {p : ℕ} {k : ℤ} (hη : ∀ᵐ s ∂η, s ∈ linearizationDistanceGroupInterval p k) :
    scalarCollisionMass η η (4 * dyadicRadius p) 0 = (η univ) ^ (2 : ℕ) :=
  scalarCollisionMass_self_eq_mass_sq_of_diameter η hη
    (fun _ hs _ hs' ↦ linearization_group_interval_diameter hs hs')

theorem scalar_group_neighbors_card_le {I : Finset ℤ} (k : ℤ) :
    ((I.filter (fun k' ↦ |k - k'| ≤ 4)).card : ℝ) ≤ 9 := by
  have hsubset : I.filter (fun k' ↦ |k - k'| ≤ 4) ⊆ Finset.Icc (k - 4) (k + 4) := by
    intro k' hk'
    have h := abs_le.mp (Finset.mem_filter.mp hk').2
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have h := Finset.card_le_card hsubset
  have hcard : (Finset.Icc (k - 4) (k + 4)).card = 9 := by
    rw [Int.card_Icc]
    have heq : k + 4 + 1 - (k - 4) = (9 : ℤ) := by ring
    rw [heq]
    norm_num
  rw [hcard] at h
  exact_mod_cast h

end FalconerThetaGauge
