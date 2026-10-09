module

public import FalconerThetaGauge.ScalarEnergyBinning
public import Mathlib.Data.Int.Interval

/-!
# Shift and dilation bounds in Lemma 7.3

The shifted pair sets are actual unions of half-open bin rectangles. Their
mass is an exact discrete correlation, so countable Cauchy--Schwarz proves
the manuscript's constants `4` and `2L+1` without discarding endpoint atoms.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal

namespace FalconerThetaGauge

/-- The exact pairs whose integer bin indices differ by `m`. -/
def scalarBinShiftPairs (h : ℝ) (m : ℤ) : Set (ℝ × ℝ) :=
  ⋃ j : ℤ, scalarBin h j ×ˢ scalarBin h (j - m)

theorem measurableSet_scalarBinShiftPairs (h : ℝ) (m : ℤ) :
    MeasurableSet (scalarBinShiftPairs h m) :=
  MeasurableSet.iUnion fun j ↦ (measurableSet_scalarBin h j).prod (measurableSet_scalarBin h _)

/-- The true measure of a bin-index shift is its exact countable mass correlation. -/
theorem measure_scalarBinShiftPairs (η ζ : Measure ℝ) [SFinite ζ]
    {h : ℝ} (hh : 0 < h) (m : ℤ) :
    η.prod ζ (scalarBinShiftPairs h m) =
      ∑' j : ℤ, scalarBinMass η h j * scalarBinMass ζ h (j - m) := by
  have hdisj : Pairwise (Disjoint on fun j : ℤ ↦ scalarBin h j ×ˢ scalarBin h (j - m)) := by
    intro j k hjk
    exact (scalarBin_pairwise_disjoint hh hjk).set_prod_left _ _
  rw [scalarBinShiftPairs, measure_iUnion hdisj (fun j ↦
    (measurableSet_scalarBin h j).prod (measurableSet_scalarBin h _))]
  simp only [Measure.prod_prod, scalarBinMass]

theorem tsum_scalarBinMass_shift_square (η : Measure ℝ) (h : ℝ) (m : ℤ) :
    (∑' j : ℤ, scalarBinMass η h (j - m) ^ (2 : ℕ)) = scalarBinSquareMass η h :=
  (Equiv.subRight m).tsum_eq (fun j ↦ scalarBinMass η h j ^ (2 : ℕ))

/-- A shifted cross-bin correlation is bounded by the two true bin-square masses. -/
theorem measure_scalarBinShiftPairs_le (η ζ : Measure ℝ) [SFinite ζ]
    {h : ℝ} (hh : 0 < h) (m : ℤ) :
    η.prod ζ (scalarBinShiftPairs h m) ≤
      scalarBinSquareMass η h ^ (1 / 2 : ℝ) * scalarBinSquareMass ζ h ^ (1 / 2 : ℝ) := by
  rw [measure_scalarBinShiftPairs η ζ hh m]
  simpa only [tsum_scalarBinMass_shift_square, scalarBinSquareMass] using
    scalarBin_cauchy_schwarz (scalarBinMass η h) (fun j ↦ scalarBinMass ζ h (j - m))

/-- Each self-correlation costs at most the unshifted bin-square mass. -/
theorem measure_scalarBinShiftPairs_self_le (η : Measure ℝ) [SFinite η]
    {h : ℝ} (hh : 0 < h) (m : ℤ) :
    η.prod η (scalarBinShiftPairs h m) ≤ scalarBinSquareMass η h := by
  have h := measure_scalarBinShiftPairs_le η η hh m
  rw [← ENNReal.rpow_add_of_nonneg (1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num)] at h
  norm_num at h
  exact h

/-- A literal finite bin-shift cover bounds the actual pair mass by its count of shifts. -/
theorem scalar_pairMass_le_finite_bin_shifts (η : Measure ℝ) [SFinite η]
    {h : ℝ} (hh : 0 < h) (M : Finset ℤ) {S : Set (ℝ × ℝ)}
    (hS : ∀ p ∈ S, scalarBinIndex h p.1 - scalarBinIndex h p.2 ∈ M) :
    η.prod η S ≤ (M.card : ℝ≥0∞) * scalarBinSquareMass η h := by
  have hcover : S ⊆ ⋃ m ∈ M, scalarBinShiftPairs h m := by
    intro p hp
    apply mem_iUnion.2
    refine ⟨scalarBinIndex h p.1 - scalarBinIndex h p.2, mem_iUnion.2 ⟨hS p hp, ?_⟩⟩
    apply mem_iUnion.2
    refine ⟨scalarBinIndex h p.1, mem_scalarBin_index hh _, ?_⟩
    simpa only [sub_sub_cancel] using mem_scalarBin_index hh p.2
  calc
    η.prod η S ≤ η.prod η (⋃ m ∈ M, scalarBinShiftPairs h m) := measure_mono hcover
    _ ≤ ∑ m ∈ M, η.prod η (scalarBinShiftPairs h m) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _m ∈ M, scalarBinSquareMass η h :=
      Finset.sum_le_sum fun m _ ↦ measure_scalarBinShiftPairs_self_le η hh m
    _ = (M.card : ℝ≥0∞) * scalarBinSquareMass η h := by simp [nsmul_eq_mul]

/-- A shifted width-`h` collision occupies at most the four displayed integer shifts. -/
theorem scalarCollision_bin_shifts {h u : ℝ} (hh : 0 < h) (p : ℝ × ℝ)
    (hp : |p.1 - p.2 - u| ≤ h) :
    scalarBinIndex h p.1 - scalarBinIndex h p.2 ∈
      Finset.Icc (scalarBinIndex h u - 1) (scalarBinIndex h u + 2) := by
  obtain ⟨hl, hu⟩ := scalarBin_difference_bounds
    (mem_scalarBin_index hh p.1) (mem_scalarBin_index hh p.2)
  obtain ⟨hun, hnu⟩ := mem_scalarBin_index hh u
  obtain ⟨hp₁, hp₂⟩ := abs_le.1 hp
  have hm₁ : ((scalarBinIndex h u : ℤ) : ℝ) - 2 <
      ((scalarBinIndex h p.1 - scalarBinIndex h p.2 : ℤ) : ℝ) := by nlinarith
  have hm₂ : ((scalarBinIndex h p.1 - scalarBinIndex h p.2 : ℤ) : ℝ) <
      ((scalarBinIndex h u : ℤ) : ℝ) + 3 := by nlinarith
  have hi₁ : scalarBinIndex h u - 2 < scalarBinIndex h p.1 - scalarBinIndex h p.2 := by
    exact_mod_cast hm₁
  have hi₂ : scalarBinIndex h p.1 - scalarBinIndex h p.2 < scalarBinIndex h u + 3 := by
    exact_mod_cast hm₂
  exact Finset.mem_Icc.2 ⟨by omega, by omega⟩

/-- Lemma 7.3(i), with the exact source constant and all finite positive measures. -/
theorem scalarCollisionMass_shift_le_four (η : Measure ℝ) [IsFiniteMeasure η]
    {h : ℝ} (hh : 0 < h) (u : ℝ) :
    scalarCollisionMass η η h u ≤ 4 * scalarCollisionMass η η h 0 := by
  calc
    scalarCollisionMass η η h u ≤
        ((Finset.Icc (scalarBinIndex h u - 1) (scalarBinIndex h u + 2)).card : ℝ≥0∞) *
          scalarBinSquareMass η h :=
      scalar_pairMass_le_finite_bin_shifts η hh _ (fun p hp ↦ scalarCollision_bin_shifts hh p hp)
    _ = 4 * scalarBinSquareMass η h := by
      have hi : scalarBinIndex h u + 2 + 1 - (scalarBinIndex h u - 1) = (4 : ℤ) := by ring
      rw [Int.card_Icc, hi]
      norm_num
    _ ≤ 4 * scalarCollisionMass η η h 0 :=
      mul_le_mul' le_rfl (scalarBinSquareMass_le_collision η hh)

/-- A collision of width `Lh` occupies exactly the integer shift interval `[-L,L]`. -/
theorem scalarCollision_dilated_bin_shifts {h : ℝ} (hh : 0 < h) (L : ℕ)
    (p : ℝ × ℝ) (hp : |p.1 - p.2| ≤ (L : ℝ) * h) :
    scalarBinIndex h p.1 - scalarBinIndex h p.2 ∈ Finset.Icc (-(L : ℤ)) (L : ℤ) := by
  obtain ⟨hl, hu⟩ := scalarBin_difference_bounds
    (mem_scalarBin_index hh p.1) (mem_scalarBin_index hh p.2)
  obtain ⟨hp₁, hp₂⟩ := abs_le.1 hp
  have hm₁ : -(L : ℝ) - 1 < ((scalarBinIndex h p.1 - scalarBinIndex h p.2 : ℤ) : ℝ) :=
    by nlinarith
  have hm₂ : ((scalarBinIndex h p.1 - scalarBinIndex h p.2 : ℤ) : ℝ) < (L : ℝ) + 1 :=
    by nlinarith
  have hi₁ : -(L : ℤ) - 1 < scalarBinIndex h p.1 - scalarBinIndex h p.2 := by
    exact_mod_cast hm₁
  have hi₂ : scalarBinIndex h p.1 - scalarBinIndex h p.2 < (L : ℤ) + 1 := by
    exact_mod_cast hm₂
  exact Finset.mem_Icc.2 ⟨by omega, by omega⟩

/-- Lemma 7.3(ii), in fact valid also for the zero integer dilation. -/
theorem scalarCollisionMass_dilate_le (η : Measure ℝ) [IsFiniteMeasure η]
    {h : ℝ} (hh : 0 < h) (L : ℕ) :
    scalarCollisionMass η η ((L : ℝ) * h) 0 ≤
      (2 * (L : ℝ≥0∞) + 1) * scalarCollisionMass η η h 0 := by
  calc
    scalarCollisionMass η η ((L : ℝ) * h) 0 ≤
        ((Finset.Icc (-(L : ℤ)) (L : ℤ)).card : ℝ≥0∞) * scalarBinSquareMass η h := by
      apply scalar_pairMass_le_finite_bin_shifts η hh
      intro p hp
      change |p.1 - p.2 - 0| ≤ (L : ℝ) * h at hp
      simp only [sub_zero] at hp
      exact scalarCollision_dilated_bin_shifts hh L p hp
    _ = (2 * (L : ℝ≥0∞) + 1) * scalarBinSquareMass η h := by
      have hi : (L : ℤ) + 1 - (-(L : ℤ)) = ((2 * L + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [Int.card_Icc, hi, Int.toNat_natCast]
      push_cast
      rfl
    _ ≤ (2 * (L : ℝ≥0∞) + 1) * scalarCollisionMass η η h 0 :=
      mul_le_mul' le_rfl (scalarBinSquareMass_le_collision η hh)

end FalconerThetaGauge
