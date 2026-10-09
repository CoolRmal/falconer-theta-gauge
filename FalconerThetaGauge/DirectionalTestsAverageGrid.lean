module

public import FalconerThetaGauge.DirectionalTestsWidening
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval

/-!
# Exact nine-square dyadic disc cover

A closed disc of radius one generation-`d` side length lies in the nine
half-open squares neighboring the square of its center. Floor indices handle
all boundary points without a nonatomicity assumption.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- The literal three-by-three neighborhood of a point's generation-`d` square. -/
def dyadicBallCells (d : ℕ) (z : Plane) : Finset (Fin 2 → ℤ) :=
  Fintype.piFinset fun i ↦ Finset.Icc (cubeIndex d z i - 1) (cubeIndex d z i + 1)

theorem mem_dyadicBallCells_iff (d : ℕ) (z : Plane) (k : Fin 2 → ℤ) :
    k ∈ dyadicBallCells d z ↔ ∀ i, cubeIndex d z i - 1 ≤ k i ∧
      k i ≤ cubeIndex d z i + 1 := by
  simp only [dyadicBallCells, Fintype.mem_piFinset, Finset.mem_Icc]

theorem card_dyadicBallCells (d : ℕ) (z : Plane) : (dyadicBallCells d z).card = 9 := by
  rw [dyadicBallCells, Fintype.card_piFinset]
  have hi (i : Fin 2) : (Finset.Icc (cubeIndex d z i - 1) (cubeIndex d z i + 1)).card = 3 := by
    rw [Int.card_Icc, show cubeIndex d z i + 1 + 1 - (cubeIndex d z i - 1) = (3 : ℤ) by ring]
    norm_num
  simp_rw [hi]
  norm_num

/-- Each coordinate of every point of the closed disc has one of the three neighboring indices. -/
theorem cubeIndex_mem_dyadicBallCells (d : ℕ) (z : Plane) {y : Plane}
    (hy : y ∈ Metric.closedBall z (dyadicRadius d)) : cubeIndex d y ∈ dyadicBallCells d z := by
  have hp : (0 : ℝ) < 2 ^ d := by positivity
  have hpr : (2 : ℝ) ^ d * dyadicRadius d = 1 := by
    rw [dyadicRadius, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast,
      mul_inv_cancel₀ hp.ne']
  apply (mem_dyadicBallCells_iff d z _).2
  intro i
  have hd : |y i - z i| ≤ dyadicRadius d :=
    (abs_sub_coord_le_dist y z i).trans (Metric.mem_closedBall.1 hy)
  have hl : (2 : ℝ) ^ d * z i - 1 ≤ (2 : ℝ) ^ d * y i := by
    nlinarith [(abs_le.1 hd).1]
  have hu : (2 : ℝ) ^ d * y i ≤ (2 : ℝ) ^ d * z i + 1 := by
    nlinarith [(abs_le.1 hd).2]
  have hfloor₁ := Int.floor_le_floor hl
  have hfloor₂ := Int.floor_le_floor hu
  simpa only [cubeIndex, Int.floor_sub_one, Int.floor_add_one] using
    And.intro hfloor₁ hfloor₂

/-- The actual closed disc is covered by precisely nine genuine half-open dyadic squares. -/
theorem closedBall_subset_dyadicBallCells (d : ℕ) (z : Plane) :
    Metric.closedBall z (dyadicRadius d) ⊆ cellUnion d (dyadicBallCells d z) := by
  intro y hy
  exact mem_iUnion₂.mpr ⟨cubeIndex d y, cubeIndex_mem_dyadicBallCells d z hy,
    mem_dyadicCube_cubeIndex d y⟩

/-- The nine-square cover bounds the actual mass by nine times the heaviest cell. -/
theorem real_closedBall_dyadicRadius_le_nine_maxCellMass (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) (d : ℕ) (z : Plane) :
    ρ.real (Metric.closedBall z (dyadicRadius d)) ≤ 9 * maxCellMass ρ d := by
  calc
    _ ≤ ρ.real (cellUnion d (dyadicBallCells d z)) :=
      measureReal_mono (closedBall_subset_dyadicBallCells d z)
    _ = ∑ k ∈ dyadicBallCells d z, unitCellWeight ρ d k := by
      unfold cellUnion unitCellWeight
      apply measureReal_biUnion_finset
      · intro k _ j _ hkj
        exact dyadicCube_disjoint hkj
      · intro k _
        exact measurableSet_dyadicCube d k
      · intro k _
        exact measure_ne_top ρ _
    _ ≤ ∑ _k ∈ dyadicBallCells d z, maxCellMass ρ d :=
      Finset.sum_le_sum fun k _ ↦ unitCellWeight_le_maxCellMass_all ρ hρ d k
    _ = _ := by simp [card_dyadicBallCells]

end FalconerThetaGauge
