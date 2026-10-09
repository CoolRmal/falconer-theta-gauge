module

public import FalconerThetaGauge.DirectionalTestsAverageGridMass

/-!
# Actual occupied-center counts in dyadic discs

The nine-square cover combines with the genuine occupied-descendant bound
to count the actual centers appearing in the tube test.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- The literal geometric midpoint belongs to its half-open dyadic square. -/
theorem dyadicCellCenter_mem_dyadicCube (p : ℕ) (Q : Fin 2 → ℤ) :
    dyadicCellCenter p Q ∈ dyadicCube p Q := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  intro i
  change (Q i : ℝ) ≤ (2 : ℝ) ^ p * (((Q i : ℝ) + 1 / 2) / (2 : ℝ) ^ p) ∧
    (2 : ℝ) ^ p * (((Q i : ℝ) + 1 / 2) / (2 : ℝ) ^ p) < (Q i : ℝ) + 1
  rw [mul_div_cancel₀ _ hp.ne']
  constructor <;> linarith

/-- The ancestor index of the literal midpoint is precisely its coarser floor index. -/
theorem cubeIndex_dyadicCellCenter_eq_ancestor {d p : ℕ} (hdp : d ≤ p)
    (Q : Fin 2 → ℤ) : cubeIndex d (dyadicCellCenter p Q) = ancestor (p - d) Q := by
  apply mem_dyadicCube_iff.1
  apply dyadicCube_subset_ancestor d (p - d) Q
  simpa only [Nat.add_sub_of_le hdp] using dyadicCellCenter_mem_dyadicCube p Q

/-- Precisely the occupied fine cells whose literal centers lie in the closed dyadic disc. -/
def occupiedCellCentersInBall (ρ : Measure Plane) (p d : ℕ) (z : Plane) :
    Finset (Fin 2 → ℤ) :=
  (occupiedUnitCells ρ p).filter
    (fun Q ↦ dyadicCellCenter p Q ∈ Metric.closedBall z (dyadicRadius d))

/-- Every counted center belongs to a genuine occupied descendant of one of the nine squares. -/
theorem occupiedCellCentersInBall_subset_descendants (ρ : Measure Plane)
    {d p : ℕ} (hdp : d ≤ p) (z : Plane) :
    occupiedCellCentersInBall ρ p d z ⊆
      (dyadicBallCells d z).biUnion (occupiedCellDescendants ρ d p) := by
  intro Q hQ
  obtain ⟨hocc, hball⟩ := Finset.mem_filter.1 hQ
  obtain ⟨hunit, hpos⟩ := Finset.mem_filter.1 hocc
  have hparent := cubeIndex_mem_dyadicBallCells d z hball
  rw [cubeIndex_dyadicCellCenter_eq_ancestor hdp] at hparent
  exact Finset.mem_biUnion.2 ⟨ancestor (p - d) Q, hparent,
    Finset.mem_filter.2 ⟨hunit, rfl, hpos⟩⟩

/-- The actual occupied-center count in the disc satisfies the source's exact constant nine. -/
theorem occupiedCellCentersInBall_count_le_excess (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {ε : ℝ} {N d p : ℕ} (hN : 0 < N)
    (hreg : IsRegularThrough ε N ρ) (hdp : d ≤ p) (hp : p ≤ N) (z : Plane) :
    ((occupiedCellCentersInBall ρ p d z).card : ℝ) ≤
      9 * (2 : ℝ) ^ (ε * N) * (2 : ℝ) ^ ((p : ℝ) - d) *
        (2 : ℝ) ^ ((N : ℝ) * (regularMeasureExcess ρ N p - regularMeasureExcess ρ N d)) := by
  have hcard := (Finset.card_le_card
    (occupiedCellCentersInBall_subset_descendants ρ hdp z)).trans
    Finset.card_biUnion_le
  calc
    _ ≤ ∑ Q ∈ dyadicBallCells d z, ((occupiedCellDescendants ρ d p Q).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ _Q ∈ dyadicBallCells d z,
        ((2 : ℝ) ^ (ε * N) * (2 : ℝ) ^ ((p : ℝ) - d) *
          (2 : ℝ) ^ ((N : ℝ) * (regularMeasureExcess ρ N p - regularMeasureExcess ρ N d))) :=
      Finset.sum_le_sum fun Q _ ↦ occupiedCellDescendants_count_le ρ hρ hN hreg hdp hp Q
    _ = _ := by
      simp only [Finset.sum_const, card_dyadicBallCells, nsmul_eq_mul]
      norm_num
      ring

end FalconerThetaGauge
