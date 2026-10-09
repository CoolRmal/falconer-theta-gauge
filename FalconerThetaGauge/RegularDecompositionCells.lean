module

public import FalconerThetaGauge.GaugeFrostmanDyadic
public import FalconerThetaGauge.GaugeSeparatedMeasuresGeometry
public import Mathlib.Data.Fintype.Pi
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Actual terminal cells and their original measure weights

The half-open unit square has precisely `4^N` generation-`N` cells. Their
original measure weights partition its mass; this connects finite bottom-up
types to the planar measure in Lemma 5.8.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset
open scoped Classical ENNReal

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- The finite coordinate indices of the terminal cells in the unit square. -/
def unitCellIndices (N : ℕ) : Finset (Fin 2 → ℤ) :=
  Finset.univ.image (fun k : Fin 2 → Fin (2 ^ N) ↦ fun i ↦ (k i : ℤ))

theorem mem_unitCellIndices_iff (N : ℕ) (k : Fin 2 → ℤ) :
    k ∈ unitCellIndices N ↔ ∀ i, 0 ≤ k i ∧ k i < (2 : ℤ) ^ N := by
  constructor
  · intro hk
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
    intro i
    change 0 ≤ (j i : ℤ) ∧ (j i : ℤ) < (2 : ℤ) ^ N
    exact ⟨by exact_mod_cast (Nat.zero_le (j i).val), by exact_mod_cast (j i).isLt⟩
  · intro hk
    let j : Fin 2 → Fin (2 ^ N) := fun i ↦
      ⟨(k i).toNat, by
        have h := (hk i).2
        rw [← Int.toNat_of_nonneg (hk i).1] at h
        exact_mod_cast h⟩
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_univ _, ?_⟩
    funext i
    exact Int.toNat_of_nonneg (hk i).1

theorem card_unitCellIndices (N : ℕ) : (unitCellIndices N).card = 4 ^ N := by
  have hinj : Function.Injective
      (fun k : Fin 2 → Fin (2 ^ N) ↦ fun i ↦ (k i : ℤ)) := by
    intro k j h
    funext i
    apply Fin.ext
    have hi := congrFun h i
    dsimp only at hi
    exact_mod_cast hi
  rw [unitCellIndices, Finset.card_image_of_injective _ hinj, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  rw [← pow_mul, Nat.mul_comm N 2, pow_mul]
  norm_num

theorem cubeIndex_mem_unitCellIndices (N : ℕ) {x : Plane} (hx : x ∈ unitSquare) :
    cubeIndex N x ∈ unitCellIndices N := by
  apply (mem_unitCellIndices_iff N _).mpr
  intro i
  constructor
  · exact Int.floor_nonneg.mpr (mul_nonneg (by positivity) (hx i).1)
  · apply Int.floor_lt.mpr
    have h := mul_lt_mul_of_pos_left (hx i).2
      (show 0 < (2 : ℝ) ^ N by positivity)
    simpa only [cubeIndex, Int.cast_pow, Int.cast_ofNat, mul_one] using h

theorem dyadicCube_subset_unitSquare (N : ℕ) {k : Fin 2 → ℤ}
    (hk : k ∈ unitCellIndices N) : dyadicCube N k ⊆ unitSquare := by
  intro x hx i
  have hi := (mem_unitCellIndices_iff N k).mp hk i
  have hlo : (0 : ℝ) ≤ k i := by exact_mod_cast hi.1
  have hhi : (k i : ℝ) + 1 ≤ (2 : ℝ) ^ N := by
    exact_mod_cast (show k i + 1 ≤ (2 : ℤ) ^ N by omega)
  have hpow : 0 < (2 : ℝ) ^ N := by positivity
  constructor <;> nlinarith [(hx i).1, (hx i).2]

/-- These half-open cubes partition exactly the half-open unit square. -/
theorem biUnion_unitCellIndices (N : ℕ) :
    (⋃ k ∈ unitCellIndices N, dyadicCube N k) = unitSquare := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
    exact dyadicCube_subset_unitSquare N hk hxk
  · intro x hx
    exact mem_iUnion₂.mpr ⟨cubeIndex N x, cubeIndex_mem_unitCellIndices N hx,
      mem_dyadicCube_cubeIndex N x⟩

/-- The terminal weights are the original measure masses, with no reweighting. -/
def unitCellWeight (μ : Measure Plane) (N : ℕ) (k : Fin 2 → ℤ) : ℝ :=
  μ.real (dyadicCube N k)

theorem unitCellWeight_nonneg (μ : Measure Plane) (N : ℕ) (k : Fin 2 → ℤ) :
    0 ≤ unitCellWeight μ N k := measureReal_nonneg

/-- Finite additivity of the disjoint terminal cells recovers the source mass. -/
theorem sum_unitCellWeight (μ : Measure Plane) [IsFiniteMeasure μ] (N : ℕ) :
    ∑ k ∈ unitCellIndices N, unitCellWeight μ N k = μ.real unitSquare := by
  rw [← biUnion_unitCellIndices N]
  symm
  apply measureReal_biUnion_finset
  · intro k _ j _ hkj
    exact dyadicCube_disjoint hkj
  · intro k _
    exact measurableSet_dyadicCube N k
  · intro k _
    exact measure_ne_top μ (dyadicCube N k)

theorem sum_unitCellWeight_eq_one (μ : Measure Plane) [IsProbabilityMeasure μ]
    (N : ℕ) (hμ : μ unitSquare = 1) :
    ∑ k ∈ unitCellIndices N, unitCellWeight μ N k = 1 := by
  rw [sum_unitCellWeight, Measure.real, hμ, ENNReal.toReal_one]

/-- All integer child indices of one ancestor, without any support restriction. -/
def parentChildIndices (m : ℕ) (p : Fin 2 → ℤ) : Finset (Fin 2 → ℤ) :=
  (unitCellIndices m).image (fun q ↦ fun i ↦ (2 : ℤ) ^ m * p i + q i)

theorem card_parentChildIndices (m : ℕ) (p : Fin 2 → ℤ) :
    (parentChildIndices m p).card = 4 ^ m := by
  rw [parentChildIndices, Finset.card_image_of_injective, card_unitCellIndices]
  intro q q' h
  funext i
  exact add_left_cancel (congrFun h i)

theorem mem_parentChildIndices_of_ancestor_eq (m : ℕ) {k p : Fin 2 → ℤ}
    (hk : ancestor m k = p) : k ∈ parentChildIndices m p := by
  let q : Fin 2 → ℤ := fun i ↦ k i % (2 : ℤ) ^ m
  have hpow : 0 < (2 : ℤ) ^ m := by positivity
  have hq : q ∈ unitCellIndices m := by
    apply (mem_unitCellIndices_iff m q).mpr
    intro i
    exact ⟨Int.emod_nonneg _ hpow.ne', Int.emod_lt_of_pos _ hpow⟩
  apply Finset.mem_image.mpr
  refine ⟨q, hq, ?_⟩
  funext i
  have hi : k i / (2 : ℤ) ^ m = p i := congrFun hk i
  have heq := Int.emod_add_mul_ediv (k i) ((2 : ℤ) ^ m)
  rw [hi] at heq
  dsimp [q]
  linarith

/-- A family of leaf indices with one common higher ancestor has no more
than `4^m` distinct intermediate child ancestors. -/
theorem card_image_ancestor_le (S : Finset (Fin 2 → ℤ)) (a m : ℕ) (p : Fin 2 → ℤ)
    (hS : ∀ k ∈ S, ancestor (a + m) k = p) :
    (S.image (ancestor a)).card ≤ 4 ^ m := by
  rw [← card_parentChildIndices m p]
  apply Finset.card_le_card
  intro q hq
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hq
  apply mem_parentChildIndices_of_ancestor_eq
  rw [ancestor_ancestor, Nat.add_comm m a]
  exact hS k hk

/-- Equal lower ancestors have equal higher ancestors. -/
theorem ancestor_eq_of_ancestor_eq {a b : ℕ} (hab : a ≤ b) {k j : Fin 2 → ℤ}
    (hkj : ancestor a k = ancestor a j) : ancestor b k = ancestor b j := by
  have h := congrArg (ancestor (b - a)) hkj
  simpa only [ancestor_ancestor, Nat.sub_add_cancel hab] using h

/-- A monotone sampled-height schedule supplies the nesting required by the
bottom-up original-weight type construction. -/
theorem sampled_ancestor_nested (height : ℕ → ℕ) (hheight : Monotone height)
    {i j : ℕ} (hij : i ≤ j) {k k' : Fin 2 → ℤ}
    (hkk' : ancestor (height i) k = ancestor (height i) k') :
    ancestor (height j) k = ancestor (height j) k' :=
  ancestor_eq_of_ancestor_eq (hheight hij) hkk'

/-- Any subfamily of the terminal unit-square cells has original weight at
most one when the source is a probability. -/
theorem sum_unitCellWeight_subfamily_le_one (μ : Measure Plane) [IsProbabilityMeasure μ]
    (N : ℕ) (S : Finset (Fin 2 → ℤ)) (hS : S ⊆ unitCellIndices N) :
    (∑ k ∈ S, unitCellWeight μ N k) ≤ 1 := by
  have hsum : (∑ k ∈ S, unitCellWeight μ N k) ≤ μ.real unitSquare := by
    rw [← sum_unitCellWeight μ N]
    exact Finset.sum_le_sum_of_subset_of_nonneg hS (fun k _ _ ↦ unitCellWeight_nonneg μ N k)
  have hmass : μ.real unitSquare ≤ 1 := by
    simp
  exact hsum.trans hmass

/-- The actual planar carrier of a finite family of terminal cells. -/
def cellUnion (N : ℕ) (S : Finset (Fin 2 → ℤ)) : Set Plane :=
  ⋃ k ∈ S, dyadicCube N k

theorem measurableSet_cellUnion (N : ℕ) (S : Finset (Fin 2 → ℤ)) :
    MeasurableSet (cellUnion N S) := by
  apply MeasurableSet.iUnion
  intro k
  apply MeasurableSet.iUnion
  intro _
  exact measurableSet_dyadicCube N k

theorem dyadicCube_subset_cellUnion (N : ℕ) {S : Finset (Fin 2 → ℤ)} {k : Fin 2 → ℤ}
    (hk : k ∈ S) : dyadicCube N k ⊆ cellUnion N S := by
  intro x hx
  exact mem_iUnion₂.mpr ⟨k, hk, hx⟩

theorem cellUnion_disjoint (N : ℕ) {S T : Finset (Fin 2 → ℤ)} (hST : Disjoint S T) :
    Disjoint (cellUnion N S) (cellUnion N T) := by
  apply Set.disjoint_left.mpr
  intro x hxS hxT
  obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hxS
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxT
  by_cases hkj : k = j
  · subst j
    exact Finset.disjoint_left.mp hST hk hj
  · exact Set.disjoint_left.mp (dyadicCube_disjoint hkj) hxk hxj

/-- The mass of a carrier is exactly the sum of its original terminal weights. -/
theorem real_cellUnion (μ : Measure Plane) [IsFiniteMeasure μ]
    (N : ℕ) (S : Finset (Fin 2 → ℤ)) :
    μ.real (cellUnion N S) = ∑ k ∈ S, unitCellWeight μ N k := by
  apply measureReal_biUnion_finset
  · intro k _ j _ hkj
    exact dyadicCube_disjoint hkj
  · intro k _
    exact measurableSet_dyadicCube N k
  · intro k _
    exact measure_ne_top μ (dyadicCube N k)

/-- The restriction defining an actual part has the exact original-weight mass. -/
theorem real_restrict_cellUnion_univ (μ : Measure Plane) [IsFiniteMeasure μ]
    (N : ℕ) (S : Finset (Fin 2 → ℤ)) :
    (μ.restrict (cellUnion N S)).real univ = ∑ k ∈ S, unitCellWeight μ N k := by
  rw [Measure.real, Measure.restrict_apply_univ]
  exact real_cellUnion μ N S

/-- Restriction to a retained family leaves every retained terminal-cell mass
unchanged, as required by the source's construction. -/
theorem unitCellWeight_restrict_cellUnion_of_mem (μ : Measure Plane) (N : ℕ)
    {S : Finset (Fin 2 → ℤ)} {k : Fin 2 → ℤ} (hk : k ∈ S) :
    unitCellWeight (μ.restrict (cellUnion N S)) N k = unitCellWeight μ N k := by
  unfold unitCellWeight Measure.real
  rw [Measure.restrict_apply (measurableSet_dyadicCube N k),
    Set.inter_eq_left.mpr (dyadicCube_subset_cellUnion N hk)]

theorem dyadicCube_disjoint_cellUnion_of_not_mem (N : ℕ)
    {S : Finset (Fin 2 → ℤ)} {k : Fin 2 → ℤ} (hk : k ∉ S) :
    Disjoint (dyadicCube N k) (cellUnion N S) := by
  apply Set.disjoint_left.mpr
  intro x hxk hxS
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxS
  have hkj : k ≠ j := fun h ↦ hk (h ▸ hj)
  exact Set.disjoint_left.mp (dyadicCube_disjoint hkj) hxk hxj

/-- No new cell mass is introduced off the retained family. -/
theorem unitCellWeight_restrict_cellUnion_of_not_mem (μ : Measure Plane) (N : ℕ)
    {S : Finset (Fin 2 → ℤ)} {k : Fin 2 → ℤ} (hk : k ∉ S) :
    unitCellWeight (μ.restrict (cellUnion N S)) N k = 0 := by
  unfold unitCellWeight Measure.real
  rw [Measure.restrict_apply (measurableSet_dyadicCube N k),
    (dyadicCube_disjoint_cellUnion_of_not_mem N hk).inter_eq, measure_empty,
    ENNReal.toReal_zero]

/-- A terminal cell lies inside exactly its stated ancestor at every earlier depth. -/
theorem mem_dyadicCube_ancestor_of_mem {n N : ℕ} (hn : n ≤ N) {k : Fin 2 → ℤ}
    {x : Plane} (hx : x ∈ dyadicCube N k) :
    x ∈ dyadicCube n (ancestor (N - n) k) := by
  apply dyadicCube_subset_ancestor n (N - n) k
  simpa only [Nat.add_sub_of_le hn] using hx

/-- Intersecting a carrier with a coarser cell selects precisely the original
terminal leaves having that ancestor. -/
theorem dyadicCube_inter_cellUnion {n N : ℕ} (hn : n ≤ N) (p : Fin 2 → ℤ)
    (S : Finset (Fin 2 → ℤ)) :
    dyadicCube n p ∩ cellUnion N S =
      cellUnion N (S.filter (fun k ↦ ancestor (N - n) k = p)) := by
  ext x
  constructor
  · rintro ⟨hxp, hxS⟩
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hxS
    have hxa := mem_dyadicCube_ancestor_of_mem hn hxk
    have hkp : ancestor (N - n) k = p :=
      (mem_dyadicCube_iff.mp hxa).symm.trans (mem_dyadicCube_iff.mp hxp)
    exact mem_iUnion₂.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, hkp⟩, hxk⟩
  · intro hx
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
    obtain ⟨hkS, hkp⟩ := Finset.mem_filter.mp hk
    refine ⟨?_, mem_iUnion₂.mpr ⟨k, hkS, hxk⟩⟩
    rw [← hkp]
    exact mem_dyadicCube_ancestor_of_mem hn hxk

/-- Every coarser cell mass of an actual restricted part is the corresponding
sum of original terminal-cell weights. -/
theorem real_restrict_cellUnion_dyadicCube (μ : Measure Plane) [IsFiniteMeasure μ]
    {n N : ℕ} (hn : n ≤ N) (S : Finset (Fin 2 → ℤ)) (p : Fin 2 → ℤ) :
    (μ.restrict (cellUnion N S)).real (dyadicCube n p) =
      ∑ k ∈ S.filter (fun k ↦ ancestor (N - n) k = p), unitCellWeight μ N k := by
  unfold Measure.real
  rw [Measure.restrict_apply (measurableSet_dyadicCube n p),
    dyadicCube_inter_cellUnion hn]
  exact real_cellUnion μ N _

/-- The original mass removed from the unit square is exactly the sum over the
discarded terminal leaves. -/
theorem real_unitSquare_diff_cellUnion (μ : Measure Plane) [IsFiniteMeasure μ]
    (N : ℕ) (S : Finset (Fin 2 → ℤ)) :
    μ.real (unitSquare \ cellUnion N S) =
      ∑ k ∈ unitCellIndices N \ S, unitCellWeight μ N k := by
  have heq : unitSquare \ cellUnion N S = cellUnion N (unitCellIndices N \ S) := by
    rw [← biUnion_unitCellIndices N]
    ext x
    constructor
    · rintro ⟨hx, hxS⟩
      obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
      have hkS : k ∉ S := fun hkS ↦ hxS (mem_iUnion₂.mpr ⟨k, hkS, hxk⟩)
      exact mem_iUnion₂.mpr ⟨k, Finset.mem_sdiff.mpr ⟨hk, hkS⟩, hxk⟩
    · intro hx
      obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
      obtain ⟨hkU, hkS⟩ := Finset.mem_sdiff.mp hk
      exact ⟨mem_iUnion₂.mpr ⟨k, hkU, hxk⟩,
        fun hxS ↦ Set.disjoint_left.mp
          (dyadicCube_disjoint_cellUnion_of_not_mem N hkS) hxk hxS⟩
  rw [heq, real_cellUnion]

/-- A restricted part is still carried by the unit square. -/
theorem restrict_cellUnion_unitSquare (μ : Measure Plane) (N : ℕ)
    (S : Finset (Fin 2 → ℤ)) (hS : S ⊆ unitCellIndices N) :
    μ.restrict (cellUnion N S) unitSquare = μ (cellUnion N S) := by
  have hsub : cellUnion N S ⊆ unitSquare := by
    intro x hx
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
    exact dyadicCube_subset_unitSquare N (hS hk) hxk
  have hmeas : MeasurableSet unitSquare := by
    rw [← biUnion_unitCellIndices N]
    exact measurableSet_cellUnion N (unitCellIndices N)
  rw [Measure.restrict_apply hmeas,
    Set.inter_eq_right.mpr hsub]

end FalconerThetaGauge
