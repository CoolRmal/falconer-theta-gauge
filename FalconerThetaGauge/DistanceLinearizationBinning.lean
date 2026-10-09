module

public import FalconerThetaGauge.ScalarEnergyBinningShift

/-! # Genuine cross-collision and finite binning bounds used in source §7.7 -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Classical

namespace FalconerThetaGauge

theorem scalarCollisionMass_cross_le_three_bins (η ζ : Measure ℝ) [SFinite ζ]
    {h : ℝ} (hh : 0 < h) :
    scalarCollisionMass η ζ h 0 ≤
      3 * (scalarBinSquareMass η h ^ (1 / 2 : ℝ) *
        scalarBinSquareMass ζ h ^ (1 / 2 : ℝ)) := by
  have hcover : {p : ℝ × ℝ | |p.1 - p.2 - 0| ≤ h} ⊆
      ⋃ m ∈ Finset.Icc (-1 : ℤ) 1, scalarBinShiftPairs h m := by
    intro p hp
    have hm := scalarCollision_dilated_bin_shifts hh 1 p (by simpa using hp)
    refine mem_iUnion.mpr ⟨scalarBinIndex h p.1 - scalarBinIndex h p.2,
      mem_iUnion.mpr ⟨hm, ?_⟩⟩
    refine mem_iUnion.mpr ⟨scalarBinIndex h p.1, mem_scalarBin_index hh _, ?_⟩
    simpa only [sub_sub_cancel] using mem_scalarBin_index hh p.2
  calc
    _ ≤ η.prod ζ (⋃ m ∈ Finset.Icc (-1 : ℤ) 1, scalarBinShiftPairs h m) :=
      measure_mono hcover
    _ ≤ ∑ m ∈ Finset.Icc (-1 : ℤ) 1, η.prod ζ (scalarBinShiftPairs h m) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _m ∈ Finset.Icc (-1 : ℤ) 1,
        scalarBinSquareMass η h ^ (1 / 2 : ℝ) *
          scalarBinSquareMass ζ h ^ (1 / 2 : ℝ) :=
      Finset.sum_le_sum fun m _ ↦ measure_scalarBinShiftPairs_le η ζ hh m
    _ = _ := by norm_num [Finset.sum_const, nsmul_eq_mul, Int.card_Icc]

theorem scalarCollisionMass_cross_le_three (η ζ : Measure ℝ) [SFinite η] [SFinite ζ]
    {h : ℝ} (hh : 0 < h) :
    scalarCollisionMass η ζ h 0 ≤
      3 * (scalarCollisionMass η η h 0 ^ (1 / 2 : ℝ) *
        scalarCollisionMass ζ ζ h 0 ^ (1 / 2 : ℝ)) := by
  exact (scalarCollisionMass_cross_le_three_bins η ζ hh).trans
    (mul_le_mul' le_rfl (mul_le_mul'
      (ENNReal.rpow_le_rpow (scalarBinSquareMass_le_collision η hh) (by norm_num))
      (ENNReal.rpow_le_rpow (scalarBinSquareMass_le_collision ζ hh) (by norm_num))))

theorem scalarBinSquareMass_finsetSum_le {ι : Type*} (I : Finset ι) (η : ι → Measure ℝ)
    (h : ℝ) :
    scalarBinSquareMass (∑ i ∈ I, η i) h ≤
      (∑ i ∈ I, scalarBinSquareMass (η i) h ^ (1 / 2 : ℝ)) ^ (2 : ℕ) := by
  unfold scalarBinSquareMass scalarBinMass
  simp_rw [Measure.finsetSum_apply, pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)]
  simp_rw [Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)]
  calc
    _ ≤ ∑ i ∈ I, ∑ j ∈ I,
        (∑' k : ℤ, η i (scalarBin h k) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) *
          (∑' k : ℤ, η j (scalarBin h k) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
        scalarBin_cauchy_schwarz _ _
    _ = _ := by simp only [pow_two]

end FalconerThetaGauge
