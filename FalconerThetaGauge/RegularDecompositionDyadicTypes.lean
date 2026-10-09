/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularDecompositionCells
public import FalconerThetaGauge.RegularDecompositionSchedule

/-!
# Actual bottom-up types of dyadic cells

The finite regular decomposition uses the original planar measure weights and
the manuscript's sampled depths. The count, discard and regularity conclusions
hold for the constructed cell types at every generation up to `N`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman

/-- The actual ancestor in the reversed sampled-depth hierarchy. -/
def regularDyadicAncestor (ε : ℝ) (N j : ℕ) : (Fin 2 → ℤ) → (Fin 2 → ℤ) :=
  ancestor (regularDecompositionSampledHeight ε N j)

theorem regularDyadicAncestor_zero {ε : ℝ} {N : ℕ} (hεN : 16 ≤ ε * N) :
    regularDyadicAncestor ε N 0 = id := by
  funext x
  simp [regularDyadicAncestor, regularDecomposition_sampledHeight_zero hεN]

theorem regularDyadicAncestor_nested (ε : ℝ) (N : ℕ) :
    ∀ i j, i ≤ j → ∀ x y, regularDyadicAncestor ε N i x = regularDyadicAncestor ε N i y →
      regularDyadicAncestor ε N j x = regularDyadicAncestor ε N j y := by
  intro i j hij x y hxy
  exact sampled_ancestor_nested _ (regularDecomposition_sampledHeight_monotone ε N) hij hxy

/-- Every constructed sampled parent has at most `4^Δ` actual sampled child indices. -/
theorem regularDyadicNode_child_count_le (S : Finset (Fin 2 → ℤ))
    (weight : (Fin 2 → ℤ) → ℝ) (ε : ℝ) (N w : ℕ) {j : ℕ}
    (hj : j < regularDecompositionBlockCount ε N) (x : Fin 2 → ℤ) :
    ((regularNodeFamily S weight (regularDyadicAncestor ε N) w (j + 1) x).image
      (regularDyadicAncestor ε N j)).card ≤ 4 ^ regularDecompositionBlockLength ε N := by
  let a := regularDecompositionSampledHeight ε N j
  let b := regularDecompositionSampledHeight ε N (j + 1)
  have hab : a ≤ b := regularDecomposition_sampledHeight_monotone ε N (by omega)
  have hcount : ((regularNodeFamily S weight (regularDyadicAncestor ε N) w (j + 1) x).image
      (ancestor a)).card ≤ 4 ^ (b - a) := by
    apply card_image_ancestor_le _ a (b - a) (ancestor b x)
    intro y hy
    rw [Nat.add_sub_of_le hab]
    exact ancestor_eq_of_mem_regularNodeFamily S weight (regularDyadicAncestor ε N) w
      (j + 1) hy
  exact hcount.trans (Nat.pow_le_pow_right (by norm_num)
    (regularDecomposition_sampledHeight_gap_le ε N hj))

/-- The actual terminal cells surviving the first discard. -/
def regularDyadicHeavyCells (μ : Measure Plane) (N : ℕ) : Finset (Fin 2 → ℤ) :=
  heavyTerminalCells (unitCellIndices N) (unitCellWeight μ N) N

/-- The actual complete bottom-up type of each terminal cell. -/
def regularDyadicType (μ : Measure Plane) (ε : ℝ) (N : ℕ) : (Fin 2 → ℤ) → List ℕ :=
  regularLeafType (regularDyadicHeavyCells μ N) (unitCellWeight μ N)
    (regularDyadicAncestor ε N) (regularDecompositionBucketWidth ε N)
      (regularDecompositionBlockCount ε N)

/-- The actual terminal cells surviving both discards, with whole type fibers retained. -/
def regularDyadicRetainedCells (μ : Measure Plane) (ε κ : ℝ) (N : ℕ) :
    Finset (Fin 2 → ℤ) :=
  retainedRegularLeaves (regularDyadicHeavyCells μ N) (unitCellWeight μ N)
    (regularDyadicType μ ε N) κ N

/-- The actual depth-`N-m` ancestor fiber of a constructed type, measured with original weights. -/
def regularDyadicGenerationFamily (μ : Measure Plane) (ε : ℝ) (N m : ℕ)
    (x : Fin 2 → ℤ) : Finset (Fin 2 → ℤ) :=
  regularIntermediateFamily (regularDyadicHeavyCells μ N) (unitCellWeight μ N)
    (regularDyadicAncestor ε N) (regularDecompositionBucketWidth ε N)
      (regularDecompositionBlockCount ε N) (ancestor m) x

theorem regularDyadicHeavyCells_subset (μ : Measure Plane) (N : ℕ) :
    regularDyadicHeavyCells μ N ⊆ unitCellIndices N := Finset.filter_subset _ _

theorem regularDyadicHeavyCells_positive (μ : Measure Plane) (N : ℕ) :
    ∀ x ∈ regularDyadicHeavyCells μ N, 0 < unitCellWeight μ N x :=
  heavyTerminalCells_positive _ _ _

theorem regularDyadicHeavyCells_total_le_one (μ : Measure Plane) [IsProbabilityMeasure μ]
    (N : ℕ) : (∑ x ∈ regularDyadicHeavyCells μ N, unitCellWeight μ N x) ≤ 1 :=
  sum_unitCellWeight_subfamily_le_one μ N _ (regularDyadicHeavyCells_subset μ N)

/-- The actual number of complete types satisfies the literal (P2) budget. -/
theorem regularDyadicType_count_le (μ : Measure Plane) [IsProbabilityMeasure μ]
    {ε κ : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) {N : ℕ} (hεN : 16 ≤ ε * N)
    (hbudget : Real.log (49 / ε) / Real.log 2 + (333 / 100 : ℝ) * (8 / ε + 1) ≤ κ * N / 4) :
    (((regularDyadicHeavyCells μ N).image (regularDyadicType μ ε N)).card : ℝ) ≤
      (2 : ℝ) ^ (κ * N / 4) := by
  exact heavyTerminalCells_type_count_le (unitCellIndices N) (unitCellWeight μ N)
    (regularDyadicAncestor ε N) hε hε₁ N hεN (fun x _ ↦ unitCellWeight_nonneg μ N x)
    (sum_unitCellWeight_subfamily_le_one μ N _ (Finset.Subset.refl _))
    (regularDyadicAncestor_zero hεN) (regularDyadicAncestor_nested ε N)
    (fun j hj x _ ↦ regularDyadicNode_child_count_le _ _ ε N _ hj x) hbudget

/-- The two actual discards lose at most `2 R^(-κ/4)` original measure mass. -/
theorem regularDyadicType_discarded_mass_le (μ : Measure Plane) [IsProbabilityMeasure μ]
    {ε κ : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (hκ : κ ≤ 4) {N : ℕ}
    (hεN : 16 ≤ ε * N)
    (hbudget : Real.log (49 / ε) / Real.log 2 + (333 / 100 : ℝ) * (8 / ε + 1) ≤ κ * N / 4) :
    (∑ x ∈ unitCellIndices N \ regularDyadicRetainedCells μ ε κ N, unitCellWeight μ N x) ≤
      2 * (2 : ℝ) ^ (-(κ * N / 4)) := by
  exact regularDecomposition_discarded_mass_le _ _ _ κ N hκ
    (card_unitCellIndices N).le (regularDyadicType_count_le μ hε hε₁ hεN hbudget)

/-- Every occupied intermediate generation of a complete type has original masses
comparable by the required factor `R^ε`. -/
theorem regularDyadicGeneration_mass_comparable (μ : Measure Plane) [IsProbabilityMeasure μ]
    {ε : ℝ} {N m : ℕ} (hεN : 16 ≤ ε * N) (hm : m ≤ N)
    {x y : Fin 2 → ℤ} (hx : x ∈ regularDyadicHeavyCells μ N)
    (hy : y ∈ regularDyadicHeavyCells μ N)
    (htype : regularDyadicType μ ε N x = regularDyadicType μ ε N y) :
    (∑ z ∈ regularDyadicGenerationFamily μ ε N m x, unitCellWeight μ N z) <
      (2 : ℝ) ^ (ε * N) *
        ∑ z ∈ regularDyadicGenerationFamily μ ε N m y, unitCellWeight μ N z := by
  obtain ⟨j, hj, hlo, hhi⟩ := regularDecomposition_sampledHeight_cover hεN hm
  let d := regularDecompositionBlockLength ε N
  let w := regularDecompositionBucketWidth ε N
  have hcard : ((regularNodeFamily (regularDyadicHeavyCells μ N) (unitCellWeight μ N)
      (regularDyadicAncestor ε N) w (j + 1) x).image (regularDyadicAncestor ε N j)).card ≤
        2 ^ (2 * d) := by
    rw [pow_mul]
    exact regularDyadicNode_child_count_le _ _ ε N w hj x
  have hcomp := regularIntermediateFamily_mass_comparable _ _ (regularDyadicAncestor ε N)
    (regularDecomposition_bucketWidth_pos hεN) (regularDyadicHeavyCells_positive μ N)
    (regularDyadicHeavyCells_total_le_one μ N) (regularDyadicAncestor_zero hεN)
    (regularDyadicAncestor_nested ε N) hj.le (ancestor m)
    (fun x y hxy ↦ ancestor_eq_of_ancestor_eq hlo hxy)
    (fun x y hxy ↦ ancestor_eq_of_ancestor_eq hhi hxy) hx hy htype (2 * d) hcard
  exact hcomp.trans_le (mul_le_mul_of_nonneg_right
    (regularDecomposition_regularity_factor_lt hεN).le
    (Finset.sum_nonneg (fun z _ ↦ unitCellWeight_nonneg μ N z)))

end FalconerThetaGauge
