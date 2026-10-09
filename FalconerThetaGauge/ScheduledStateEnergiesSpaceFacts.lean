module

public import FalconerThetaGauge.ScheduledStateEnergiesSpaceRecurrence

/-! # Literal child lists and geometry for the final analytic space-splitting move -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem profileNearStart_strict_geometry {A : ℕ → ℝ} {q N δ b e a v : ℕ}
    (hδq : δ ≤ q) (hlong : 100 * q < v - a)
    (hsmall : 2 * profileLongestTestLength A q N b e a < v - a) :
    a < profileNearStart A q N δ b e a v ∧
      profileNearStart A q N δ b e a v ≤ v ∧
      v - profileNearStart A q N δ b e a v =
        2 * max (profileLongestTestLength A q N b e a) δ := by
  unfold profileNearStart
  omega

/-- Every true discrepancy child uses a sublist of the parent's actual remaining tests. -/
theorem profileScheduledTests_subset_remaining_for_far {A : ℕ → ℝ}
    {q N b e a n v : ℕ} (hq : 0 < q) (hba : b ≤ a) (han : a < n)
    (hve : v ≤ e) (he : e ≤ N) :
    profileScheduledTests A q N n v ⊆ profileRemainingTests A q N b e a := by
  intro test htest
  have hlist := profileScheduledTests_mono A q N (hba.trans han.le) hve htest
  exact mem_filter.mpr ⟨hlist,
    han.trans (profileScheduledTests_anchor_strict hq (hve.trans he) htest)⟩

/-- Dropping to the child's actual list can only increase the literal passing distance energy. -/
theorem scheduledDistanceEnergy_remaining_le_far_state (ρ : Measure Plane)
    [IsFiniteMeasure ρ] (A : ℕ → ℝ) {q N b e a n v : ℕ} (hq : 0 < q)
    (hba : b ≤ a) (han : a < n) (hve : v ≤ e) (he : e ≤ N)
    (E : ℝ) (levels i : ℕ) {P Q : Fin 2 → ℤ}
    (hP : P ∈ occupiedUnitCells ρ n) (hQ : Q ∈ occupiedUnitCells ρ n)
    (hsep : SeparatedDyadicCells n P Q) :
    scheduledDistanceEnergy ρ ρ (dyadicCube n P) (dyadicCube n Q) E
        (directionalLevelWidth levels i) (profileRemainingTests A q N b e a)
        (profileRemainingTests A q N b e a) v ≤
      profileDistanceStateEnergy ρ A q N E levels i n v := by
  have hsub := profileScheduledTests_subset_remaining_for_far (A := A) hq hba han hve he
  have hh := scheduledDistanceEnergy_mono ρ ρ (measurableSet_dyadicCube n P)
    (measurableSet_dyadicCube n Q)
    (mul_pos (by norm_num : (0 : ℝ) < 500) (dyadicRadius_pos n))
    (fun _x hx _y hy ↦ (dist_bounds_of_separatedDyadicCells hsep hx hy).1)
    E (le_refl (directionalLevelWidth levels i)) hsub hsub v
  exact hh.trans (scheduledDistanceEnergy_le_profileDistanceStateEnergy ρ A q N E
    levels i n v hP hQ hsep)

/-- The actual far passing set is controlled by the genuine next-level discrepancy child. -/
theorem regularRemainingDistanceEnergy_le_far_child (ρ : Measure Plane)
    [IsFiniteMeasure ρ] (θ : ℝ) {N b e a n v : ℕ} (hN : 0 < N)
    (hba : b ≤ a) (han : a < n) (hve : v ≤ e) (he : e ≤ N)
    (i : ℕ) {P Q : Fin 2 → ℤ}
    (hP : P ∈ occupiedUnitCells ρ n) (hQ : Q ∈ occupiedUnitCells ρ n)
    (hsep : SeparatedDyadicCells n P Q) :
    scheduledDistanceEnergy ρ ρ (dyadicCube n P) (dyadicCube n Q)
        (tolerance θ N * N) (directionalLevelWidth (maskLevelCount θ N) (i + 1))
        (profileRemainingTests (regularMeasureExcess ρ N) (blockCount θ N) N b e a)
        (profileRemainingTests (regularMeasureExcess ρ N) (blockCount θ N) N b e a) v ≤
      regularMeasureStateEnergy ρ θ N (i + 1) (.discrepancy n v) :=
  scheduledDistanceEnergy_remaining_le_far_state ρ (regularMeasureExcess ρ N)
    (blockCount_pos θ hN) hba han hve he (tolerance θ N * N)
    (maskLevelCount θ N) (i + 1) hP hQ hsep

end FalconerThetaGauge
