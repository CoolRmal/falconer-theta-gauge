module

public import FalconerThetaGauge.MaskedFourierEnergy
public import FalconerThetaGauge.RegularMeasureExcessCount
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # The actual Fourier amplitudes split over occupied dyadic descendants -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem maskedFourierAmplitude_biUnion (ρ : Measure Plane) [IsFiniteMeasure ρ]
    {ι : Type*} (s : Finset ι) (X : ι → Set Plane)
    (hX : ∀ i ∈ s, MeasurableSet (X i)) (hdisj : Set.Pairwise (↑s) (Disjoint on X))
    {b : Plane → UnitCircle → ℝ} (hb : Measurable (uncurry b))
    (hb₁ : ∀ x w, |b x w| ≤ 1) (r : ℝ) (w : UnitCircle) :
    maskedFourierAmplitude ρ (⋃ i ∈ s, X i) b r w =
      ∑ i ∈ s, maskedFourierAmplitude ρ (X i) b r w := by
  unfold maskedFourierAmplitude
  exact integral_biUnion_finset s hX hdisj
    (fun i _ ↦ integrable_maskedFourier_integrand ρ (X i) hb hb₁ r w)

theorem maskedFourierAmplitude_eq_zero_of_real_mass_zero (ρ : Measure Plane)
    [IsFiniteMeasure ρ] {X : Set Plane} (hX : ρ.real X = 0)
    {b : Plane → UnitCircle → ℝ} (hb : Measurable (uncurry b))
    (hb₁ : ∀ x w, |b x w| ≤ 1) (r : ℝ) (w : UnitCircle) :
    maskedFourierAmplitude ρ X b r w = 0 := by
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa only [hX] using
    norm_maskedFourierAmplitude_le_mass ρ X hb hb₁ r w) (norm_nonneg _)

theorem maskedFourierAmplitude_cellUnion (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (p : ℕ) (s : Finset (Fin 2 → ℤ)) {b : Plane → UnitCircle → ℝ}
    (hb : Measurable (uncurry b)) (hb₁ : ∀ x w, |b x w| ≤ 1) (r : ℝ) (w : UnitCircle) :
    maskedFourierAmplitude ρ (cellUnion p s) b r w =
      ∑ P ∈ s, maskedFourierAmplitude ρ (dyadicCube p P) b r w :=
  maskedFourierAmplitude_biUnion ρ s (dyadicCube p) (fun P _ ↦ measurableSet_dyadicCube p P)
    (fun _P _ _Q _ hPQ ↦ dyadicCube_disjoint hPQ) hb hb₁ r w

/-- The actual finite cell expansion used before orthogonality and space splitting. -/
theorem maskedFourierAmplitude_occupiedCellDescendants (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {a p : ℕ} (hap : a ≤ p)
    (X : Fin 2 → ℤ) {b : Plane → UnitCircle → ℝ} (hb : Measurable (uncurry b))
    (hb₁ : ∀ x w, |b x w| ≤ 1) (r : ℝ) (w : UnitCircle) :
    maskedFourierAmplitude ρ (dyadicCube a X) b r w =
      ∑ P ∈ occupiedCellDescendants ρ a p X,
        maskedFourierAmplitude ρ (dyadicCube p P) b r w := by
  have hρU : ρ.restrict unitSquare = ρ := by
    apply Measure.restrict_eq_self_of_ae_mem
    exact (ae_mem_iff_measure_eq measurableSet_unitSquare.nullMeasurableSet).mpr
      (by simpa only [measure_univ] using hρ)
  have hre : ρ.restrict (dyadicCube a X ∩ unitSquare) = ρ.restrict (dyadicCube a X) := by
    rw [← Measure.restrict_restrict (measurableSet_dyadicCube a X), hρU]
  let S := (unitCellIndices p).filter (fun P ↦ ancestor (p - a) P = X)
  have hO : occupiedCellDescendants ρ a p X ⊆ S := by
    intro P hP
    obtain ⟨hP, hanc, _⟩ := mem_filter.mp hP
    exact mem_filter.mpr ⟨hP, hanc⟩
  calc
    _ = maskedFourierAmplitude ρ (dyadicCube a X ∩ unitSquare) b r w := by
      unfold maskedFourierAmplitude
      rw [hre]
    _ = maskedFourierAmplitude ρ (cellUnion p S) b r w := by
      rw [← biUnion_unitCellIndices p]
      change maskedFourierAmplitude ρ (dyadicCube a X ∩ cellUnion p (unitCellIndices p))
        b r w = _
      rw [dyadicCube_inter_cellUnion hap]
    _ = ∑ P ∈ S, maskedFourierAmplitude ρ (dyadicCube p P) b r w :=
      maskedFourierAmplitude_cellUnion ρ p S hb hb₁ r w
    _ = _ := by
      symm
      apply sum_subset hO
      intro P hPS hPO
      have hmass : unitCellWeight ρ p P = 0 := by
        have hP := mem_filter.mp hPS
        have hh : ¬0 < unitCellWeight ρ p P := by
          intro hh
          exact hPO (mem_filter.mpr ⟨hP.1, hP.2, hh⟩)
        exact le_antisymm (le_of_not_gt hh) (unitCellWeight_nonneg ρ p P)
      exact maskedFourierAmplitude_eq_zero_of_real_mass_zero ρ hmass hb hb₁ r w

end FalconerThetaGauge
