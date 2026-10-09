/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerThetaGauge.GaugeFrostman
public import Mathlib.Data.Finset.Pi
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Atomic gauge Frostman approximations

Adapted from `FalconerPacking.WeightMeasure`, `FalconerPacking.Restriction`,
and `FalconerPacking.OccupiedCubes` (original attribution preserved above),
`CoolRmal/falconer-packing` commit `70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/tree/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking

Positive finite gauge weights are normalized to genuine probability measures.
Compactness supplies occupied finite dyadic covers and selected atoms inside the
set. Cube estimates imply ball estimates with a factor of four.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerThetaGauge.GaugeFrostman

/-- A bound on the mass of the dyadic cubes of generation `n` gives a bound on the mass of balls
of radius at most `2⁻ⁿ⁻¹`: such a ball meets at most four cubes. -/
theorem measure_ball_le_of_cube_bound {μ : Measure (EuclideanSpace ℝ (Fin 2))} {n : ℕ} {x : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    {M : ℝ≥0∞} (hr : 0 < r) (hrn : r ≤ (2 : ℝ) ^ (-((n : ℝ) + 1)))
    (hM : ∀ k, μ (dyadicCube n k) ≤ M) : μ (Metric.ball x r) ≤ 4 * M := by
  classical
  obtain ⟨k, hk⟩ := exists_cubeIndex_pair n x hr hrn
  have hsub : Metric.ball x r
      ⊆ ⋃ b : Fin 2 → Bool, dyadicCube n (fun i ↦ k i + if b i then 1 else 0) := by
    intro y hy
    refine Set.mem_iUnion.2 ⟨fun i ↦ decide (cubeIndex n y i = k i + 1), ?_⟩
    refine mem_dyadicCube_iff.2 (funext fun i ↦ ?_)
    rcases hk y hy i with h | h
    · simp [h]
    · simp [h]
  calc μ (Metric.ball x r)
      ≤ μ (⋃ b : Fin 2 → Bool, dyadicCube n (fun i ↦ k i + if b i then 1 else 0)) :=
        measure_mono hsub
    _ ≤ ∑ b : Fin 2 → Bool, μ (dyadicCube n (fun i ↦ k i + if b i then 1 else 0)) :=
        measure_iUnion_fintype_le _ _
    _ ≤ (Finset.univ : Finset (Fin 2 → Bool)).card • M :=
        Finset.sum_le_card_nsmul _ _ _ fun b _ ↦ hM _
    _ = 4 * M := by
        simp [Finset.card_univ, nsmul_eq_mul]


/-- The measure carried by a weight assignment: one point mass in each occupied cube. -/
def weightMeasure (S : Finset (Fin 2 → ℤ)) (pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)) (w : (Fin 2 → ℤ) → ℝ) :
    Measure (EuclideanSpace ℝ (Fin 2)) :=
  ∑ k' ∈ S, Real.toNNReal (w k') • Measure.dirac (pt k')

theorem weightMeasure_apply (S : Finset (Fin 2 → ℤ)) (pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2))
    (w : (Fin 2 → ℤ) → ℝ) {A : Set (EuclideanSpace ℝ (Fin 2))} (_hA : MeasurableSet A) :
    weightMeasure S pt w A =
      ∑ k' ∈ S, ENNReal.ofReal (w k') * Measure.dirac (pt k') A := by
  rw [weightMeasure, Measure.finsetSum_apply]
  simp only [Measure.coe_nnreal_smul_apply, ENNReal.ofNNReal_toNNReal]

/-- The total mass is the total weight. -/
theorem weightMeasure_univ (S : Finset (Fin 2 → ℤ)) (pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2))
    {w : (Fin 2 → ℤ) → ℝ} (hw : ∀ k, 0 ≤ w k) :
    weightMeasure S pt w univ = ENNReal.ofReal (∑ k' ∈ S, w k') := by
  rw [weightMeasure_apply _ _ _ MeasurableSet.univ]
  simp only [Measure.dirac_apply_of_mem (mem_univ _), mul_one]
  exact (ENNReal.ofReal_sum_of_nonneg fun k' _ ↦ hw k').symm

/-- Regard the finite atomic measure as a finite measure in mathlib's bundled type. -/
def weightFiniteMeasure (S : Finset (Fin 2 → ℤ))
    (pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)) (w : (Fin 2 → ℤ) → ℝ) :
    FiniteMeasure (EuclideanSpace ℝ (Fin 2)) :=
  ⟨weightMeasure S pt w, by
    rw [weightMeasure]
    infer_instance⟩

@[simp]
theorem weightFiniteMeasure_toMeasure (S : Finset (Fin 2 → ℤ))
    (pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)) (w : (Fin 2 → ℤ) → ℝ) :
    (weightFiniteMeasure S pt w : Measure (EuclideanSpace ℝ (Fin 2))) =
      weightMeasure S pt w :=
  rfl

/-- Normalize a nonzero finite Frostman construction to a probability measure.  The definition is
total; as in mathlib, the zero input is sent to a fixed point mass. -/
def weightProbabilityMeasure (S : Finset (Fin 2 → ℤ))
    (pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)) (w : (Fin 2 → ℤ) → ℝ) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)) :=
  (weightFiniteMeasure S pt w).normalize

/-- Positive total weight makes the atomic measure nonzero. -/
theorem weightFiniteMeasure_ne_zero (S : Finset (Fin 2 → ℤ))
    (pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)) {w : (Fin 2 → ℤ) → ℝ}
    (hw : ∀ k, 0 ≤ w k) (hmass : 0 < ∑ k' ∈ S, w k') :
    weightFiniteMeasure S pt w ≠ 0 := by
  intro hzero
  have huniv : weightMeasure S pt w univ = 0 := by
    rw [← weightFiniteMeasure_toMeasure]
    simp [hzero]
  rw [weightMeasure_univ S pt hw, ENNReal.ofReal_eq_zero] at huniv
  exact (not_le_of_gt hmass) huniv

/-- On a nonzero construction, normalization divides the original measure by its total mass. -/
theorem weightProbabilityMeasure_toMeasure (S : Finset (Fin 2 → ℤ))
    (pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)) {w : (Fin 2 → ℤ) → ℝ}
    (hw : ∀ k, 0 ≤ w k) (hmass : 0 < ∑ k' ∈ S, w k') :
    (weightProbabilityMeasure S pt w : Measure (EuclideanSpace ℝ (Fin 2))) =
      (weightFiniteMeasure S pt w).mass⁻¹ • weightMeasure S pt w := by
  rw [weightProbabilityMeasure,
    (weightFiniteMeasure S pt w).toMeasure_normalize_eq_of_nonzero
      (weightFiniteMeasure_ne_zero S pt hw hmass), weightFiniteMeasure_toMeasure]

/-- The bundled finite measure has the expected total mass. -/
theorem weightFiniteMeasure_mass (S : Finset (Fin 2 → ℤ))
    (pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)) {w : (Fin 2 → ℤ) → ℝ}
    (hw : ∀ k, 0 ≤ w k) :
    (weightFiniteMeasure S pt w).mass = Real.toNNReal (∑ k' ∈ S, w k') := by
  apply ENNReal.coe_injective
  rw [FiniteMeasure.ennreal_mass, weightFiniteMeasure_toMeasure,
    weightMeasure_univ S pt hw]
  rfl

/-- If every selected atom lies in `K`, the atomic measure gives zero mass to its complement. -/
theorem weightMeasure_compl_eq_zero {S : Finset (Fin 2 → ℤ)}
    {pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)} {w : (Fin 2 → ℤ) → ℝ}
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : MeasurableSet K)
    (hpt : ∀ k ∈ S, pt k ∈ K) :
    weightMeasure S pt w Kᶜ = 0 := by
  rw [weightMeasure_apply S pt w hK.compl]
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  simp [Measure.dirac_apply, hpt k hk]

/-- Normalization preserves the fact that all mass is carried by `K`. -/
theorem weightProbabilityMeasure_compl_eq_zero {S : Finset (Fin 2 → ℤ)}
    {pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)} {w : (Fin 2 → ℤ) → ℝ}
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : MeasurableSet K)
    (hw : ∀ k, 0 ≤ w k) (hmass : 0 < ∑ k' ∈ S, w k')
    (hpt : ∀ k ∈ S, pt k ∈ K) :
    (weightProbabilityMeasure S pt w : Measure (EuclideanSpace ℝ (Fin 2))) Kᶜ = 0 := by
  rw [weightProbabilityMeasure_toMeasure S pt hw hmass,
    Measure.coe_nnreal_smul_apply, weightMeasure_compl_eq_zero hK hpt, mul_zero]

section CubeMass

variable {S : Finset (Fin 2 → ℤ)} {n : ℕ} {pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)} {w : (Fin 2 → ℤ) → ℝ}

/-- A chosen point of an occupied cube lies in a cube of a coarser generation exactly when that
cube is its ancestor. -/
theorem mem_dyadicCube_iff_ancestor {i : ℕ} (hin : i ≤ n) {k' c : Fin 2 → ℤ}
    (hpt : pt k' ∈ dyadicCube n k') :
    pt k' ∈ dyadicCube i c ↔ ancestor (n - i) k' = c := by
  constructor
  · intro hmem
    have hanc : pt k' ∈ dyadicCube i (ancestor (n - i) k') := by
      have harith : i + (n - i) = n := by omega
      have := dyadicCube_subset_ancestor i (n - i) k'
      rw [harith] at this
      exact this hpt
    by_contra hne
    exact absurd (mem_dyadicCube_iff.1 hmem) (by
      rw [mem_dyadicCube_iff.1 hanc] at *
      exact fun h ↦ hne h)
  · intro hanc
    have harith : i + (n - i) = n := by omega
    have hsub := dyadicCube_subset_ancestor i (n - i) k'
    rw [harith] at hsub
    rw [← hanc]
    exact hsub hpt

/-- **The measure of a dyadic cube is its combinatorial mass.** -/
theorem weightMeasure_dyadicCube (hw : ∀ k, 0 ≤ w k)
    (hpt : ∀ k' ∈ S, pt k' ∈ dyadicCube n k') {i : ℕ} (hin : i ≤ n) (c : Fin 2 → ℤ) :
    weightMeasure S pt w (dyadicCube i c) = ENNReal.ofReal (cubeMass S n i w c) := by
  classical
  rw [weightMeasure_apply _ _ _ (measurableSet_dyadicCube i c), cubeMass,
    ENNReal.ofReal_sum_of_nonneg fun k' _ ↦ hw k']
  simp only [Measure.dirac_apply, Set.indicator_apply, Pi.one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun k' hk' ↦ ?_
  by_cases hmem : pt k' ∈ dyadicCube i c
  · rw [ite_eq_left hmem, ite_eq_left ((mem_dyadicCube_iff_ancestor hin (hpt k' hk')).1 hmem)]
  · rw [ite_eq_right hmem, ite_eq_right (fun h ↦ hmem ((mem_dyadicCube_iff_ancestor hin (hpt k' hk')).2 h))]

/-- The measure obeys the allowance of every generation. -/
theorem weightMeasure_dyadicCube_le {d : PositiveCapacity} (hw : ∀ k, 0 ≤ w k)
    (hpt : ∀ k' ∈ S, pt k' ∈ dyadicCube n k')
    (hbound : ∀ i ≤ n, ∀ k, cubeMass S n i w k ≤ allowance i d) {i : ℕ} (hin : i ≤ n)
    (c : Fin 2 → ℤ) :
    weightMeasure S pt w (dyadicCube i c) ≤ ENNReal.ofReal (allowance i d) := by
  rw [weightMeasure_dyadicCube hw hpt hin c]
  exact ENNReal.ofReal_le_ofReal (hbound i hin c)

/-- **A Frostman bound on balls.**  Through the four-cube bridge, the measure of a ball of radius
at most `2⁻ⁿ⁻¹` is at most `4` times the allowance of generation `n`. -/
theorem weightMeasure_ball_le {d : PositiveCapacity} (hw : ∀ k, 0 ≤ w k)
    (hpt : ∀ k' ∈ S, pt k' ∈ dyadicCube n k')
    (hbound : ∀ i ≤ n, ∀ k, cubeMass S n i w k ≤ allowance i d) (x : EuclideanSpace ℝ (Fin 2)) {r : ℝ}
    (hr : 0 < r) (hrn : r ≤ (2 : ℝ) ^ (-((n : ℝ) + 1))) :
    weightMeasure S pt w (Metric.ball x r) ≤ 4 * ENNReal.ofReal (allowance n d) :=
  measure_ball_le_of_cube_bound hr hrn fun k ↦
    weightMeasure_dyadicCube_le hw hpt hbound le_rfl k

end CubeMass

/-- Normalization transfers a dyadic cube estimate, with the reciprocal total mass as the new
constant. -/
theorem weightProbabilityMeasure_dyadicCube_le {S : Finset (Fin 2 → ℤ)} {n : ℕ}
    {pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)} {w : (Fin 2 → ℤ) → ℝ} {d : PositiveCapacity}
    (hw : ∀ k, 0 ≤ w k) (hmass : 0 < ∑ k' ∈ S, w k')
    (hpt : ∀ k' ∈ S, pt k' ∈ dyadicCube n k')
    (hbound : ∀ i ≤ n, ∀ k, cubeMass S n i w k ≤ allowance i d)
    {i : ℕ} (hin : i ≤ n) (c : Fin 2 → ℤ) :
    (weightProbabilityMeasure S pt w : Measure (EuclideanSpace ℝ (Fin 2)))
        (dyadicCube i c) ≤
      ((weightFiniteMeasure S pt w).mass : ℝ≥0∞)⁻¹ * ENNReal.ofReal (allowance i d) := by
  rw [weightProbabilityMeasure_toMeasure S pt hw hmass,
    Measure.coe_nnreal_smul_apply,
    ENNReal.coe_inv ((weightFiniteMeasure S pt w).mass_nonzero_iff.mpr
      (weightFiniteMeasure_ne_zero S pt hw hmass))]
  gcongr
  exact weightMeasure_dyadicCube_le hw hpt hbound hin c

/-- Normalization transfers the four-cube ball estimate, again divided by the total mass. -/
theorem weightProbabilityMeasure_ball_le {S : Finset (Fin 2 → ℤ)} {n : ℕ}
    {pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)} {w : (Fin 2 → ℤ) → ℝ} {d : PositiveCapacity}
    (hw : ∀ k, 0 ≤ w k) (hmass : 0 < ∑ k' ∈ S, w k')
    (hpt : ∀ k' ∈ S, pt k' ∈ dyadicCube n k')
    (hbound : ∀ i ≤ n, ∀ k, cubeMass S n i w k ≤ allowance i d)
    (x : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r)
    (hrn : r ≤ (2 : ℝ) ^ (-((n : ℝ) + 1))) :
    (weightProbabilityMeasure S pt w : Measure (EuclideanSpace ℝ (Fin 2)))
        (Metric.ball x r) ≤
      ((weightFiniteMeasure S pt w).mass : ℝ≥0∞)⁻¹ *
        (4 * ENNReal.ofReal (allowance n d)) := by
  rw [weightProbabilityMeasure_toMeasure S pt hw hmass,
    Measure.coe_nnreal_smul_apply,
    ENNReal.coe_inv ((weightFiniteMeasure S pt w).mass_nonzero_iff.mpr
      (weightFiniteMeasure_ne_zero S pt hw hmass))]
  gcongr
  exact weightMeasure_ball_le hw hpt hbound x hr hrn


/-- Half the side length of a generation-`n` dyadic cube. -/
def dyadicCoverRadius (n : ℕ) : ℝ := (2 : ℝ) ^ (-((n : ℝ) + 1))

theorem dyadicCoverRadius_pos (n : ℕ) : 0 < dyadicCoverRadius n :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- The at most four generation-`n` cube indices that can meet the small ball centered at `x`. -/
def neighboringCubeIndices (n : ℕ) (x : EuclideanSpace ℝ (Fin 2)) :
    Finset (Fin 2 → ℤ) :=
  Fintype.piFinset fun i ↦
    {⌊(2 : ℝ) ^ n * (x i - dyadicCoverRadius n)⌋,
      ⌊(2 : ℝ) ^ n * (x i - dyadicCoverRadius n)⌋ + 1}

/-- In the plane there are exactly four candidate dyadic cubes around a ball center. -/
theorem card_neighboringCubeIndices (n : ℕ) (x : EuclideanSpace ℝ (Fin 2)) :
    (neighboringCubeIndices n x).card = 4 := by
  simp [neighboringCubeIndices]

theorem cubeIndex_mem_neighboringCubeIndices {n : ℕ} {x y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ Metric.ball x (dyadicCoverRadius n)) :
    cubeIndex n y ∈ neighboringCubeIndices n x := by
  rw [neighboringCubeIndices, Fintype.mem_piFinset]
  intro i
  simp only [Finset.mem_insert, Finset.mem_singleton]
  exact cubeIndex_eq_lower_or_succ n x (dyadicCoverRadius_pos n) le_rfl y hy i

/-- All cube indices supplied by a finite cover by small balls. -/
def coveringCubeIndices (n : ℕ) (t : Finset (EuclideanSpace ℝ (Fin 2))) :
    Finset (Fin 2 → ℤ) :=
  t.biUnion (neighboringCubeIndices n)

/-- Discard from the finite candidate family all cubes that do not meet `K`. -/
def occupiedCubeIndices (K : Set (EuclideanSpace ℝ (Fin 2))) (n : ℕ)
    (t : Finset (EuclideanSpace ℝ (Fin 2))) : Finset (Fin 2 → ℤ) :=
  by
    classical
    exact (coveringCubeIndices n t).filter fun k ↦ (K ∩ dyadicCube n k).Nonempty

/-- Passing from a finite ball cover to the occupied dyadic cubes loses a factor of at most four. -/
theorem card_occupiedCubeIndices_le (K : Set (EuclideanSpace ℝ (Fin 2))) (n : ℕ)
    (t : Finset (EuclideanSpace ℝ (Fin 2))) :
    (occupiedCubeIndices K n t).card ≤ 4 * t.card := by
  classical
  calc
    (occupiedCubeIndices K n t).card ≤ (coveringCubeIndices n t).card := by
      exact Finset.card_filter_le _ _
    _ ≤ t.card * 4 := by
      apply Finset.card_biUnion_le_card_mul
      intro x hx
      rw [card_neighboringCubeIndices]
    _ = 4 * t.card := Nat.mul_comm _ _

/-- A finite cover by the small balls yields a cover by the occupied candidate cubes. -/
theorem subset_iUnion_occupiedCubeIndices {K : Set (EuclideanSpace ℝ (Fin 2))} {n : ℕ}
    {t : Finset (EuclideanSpace ℝ (Fin 2))}
    (hcover : K ⊆ ⋃ x ∈ t, Metric.ball x (dyadicCoverRadius n)) :
    K ⊆ ⋃ k ∈ occupiedCubeIndices K n t, dyadicCube n k := by
  classical
  intro y hy
  obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.1 (hcover hy)
  have hcandidate : cubeIndex n y ∈ coveringCubeIndices n t := by
    rw [coveringCubeIndices, Finset.mem_biUnion]
    exact ⟨x, hxt, cubeIndex_mem_neighboringCubeIndices hyx⟩
  have hoccupied : cubeIndex n y ∈ occupiedCubeIndices K n t := by
    rw [occupiedCubeIndices, Finset.mem_filter]
    exact ⟨hcandidate, ⟨y, hy, mem_dyadicCube_cubeIndex n y⟩⟩
  exact Set.mem_iUnion₂.2
    ⟨cubeIndex n y, hoccupied, mem_dyadicCube_cubeIndex n y⟩

/-- Compactness supplies a finite cover by balls at the dyadic covering radius. -/
theorem exists_finset_ball_cover_of_isCompact {K : Set (EuclideanSpace ℝ (Fin 2))}
    (hK : IsCompact K) (n : ℕ) :
    ∃ t : Finset (EuclideanSpace ℝ (Fin 2)),
      K ⊆ ⋃ x ∈ t, Metric.ball x (dyadicCoverRadius n) := by
  obtain ⟨t, _htK, htfinite, hcover⟩ :=
    finite_cover_balls_of_compact hK (dyadicCoverRadius_pos n)
  refine ⟨htfinite.toFinset, ?_⟩
  simpa using hcover

/-- A compact set has a finite generation-`n` dyadic cover consisting only of occupied cubes,
with one selected point of the set in each cube. -/
theorem exists_occupiedCubeIndices_and_points {K : Set (EuclideanSpace ℝ (Fin 2))}
    (hK : IsCompact K) (n : ℕ) :
    ∃ (S : Finset (Fin 2 → ℤ))
      (pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)),
      K ⊆ ⋃ k ∈ S, dyadicCube n k ∧
        ∀ k ∈ S, pt k ∈ K ∩ dyadicCube n k := by
  classical
  obtain ⟨t, hcover⟩ := exists_finset_ball_cover_of_isCompact hK n
  let S := occupiedCubeIndices K n t
  have hnonempty : ∀ k ∈ S, (K ∩ dyadicCube n k).Nonempty := by
    intro k hk
    have hk' : k ∈ coveringCubeIndices n t ∧ (K ∩ dyadicCube n k).Nonempty := by
      simpa only [S, occupiedCubeIndices, Finset.mem_filter] using hk
    exact hk'.2
  let pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2) := fun k ↦
    if hk : k ∈ S then Classical.choose (hnonempty k hk) else 0
  refine ⟨S, pt, subset_iUnion_occupiedCubeIndices hcover, ?_⟩
  intro k hk
  simp only [pt, dite_eq_left hk]
  exact Classical.choose_spec (hnonempty k hk)


/-- Invert the finite mass lower bound without introducing a depth-dependent constant. -/
theorem inverse_mass_le_content_constant {H c M : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ∞)
    (h : H ≤ c * M) : M⁻¹ ≤ c * H⁻¹ := by
  calc
    M⁻¹ = c * (c * M)⁻¹ := by
      rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop), ← mul_assoc,
        ENNReal.mul_inv_cancel hc0 hctop, one_mul]
    _ ≤ c * H⁻¹ := by gcongr

/-- A compact set of positive gauge content carries a finite-depth probability
approximation with one bound valid at every dyadic generation up to that depth.
The constant depends on the set and the gauge, not the finite depth. -/
theorem exists_compact_probabilityMeasure_all_scale_estimates
    {E : Set Plane} (hE : IsCompact E) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1)
    (hcontent : 0 < gaugeContent θ E) {n : ℕ} (hn : 1 ≤ n) :
    ∃ μ : ProbabilityMeasure Plane,
      (μ : Measure Plane) Eᶜ = 0 ∧
      ∀ i ≤ n, ∀ x r, 0 < r → r ≤ dyadicCoverRadius i →
        (μ : Measure Plane) (Metric.ball x r) ≤
          (ENNReal.ofReal (gaugeDoublingConstant θ) * (gaugeContent θ E)⁻¹) *
            (4 * ENNReal.ofReal (realGauge θ (dyadicRadius i))) := by
  obtain ⟨S, pt, hcov, hpt⟩ := exists_occupiedCubeIndices_and_points hE n
  obtain ⟨w, hw, hmass, hbound, hmassbound⟩ :=
    exists_finite_gauge_weights_mass_bound hθ₀ hθ₁ S hn hcontent hcov
  have hptE : ∀ k ∈ S, pt k ∈ E := fun k hk ↦ (hpt k hk).1
  have hptcube : ∀ k ∈ S, pt k ∈ dyadicCube n k := fun k hk ↦ (hpt k hk).2
  have hmasscoe : ((weightFiniteMeasure S pt w).mass : ℝ≥0∞) =
      ENNReal.ofReal (∑ k' ∈ S, w k') := by
    rw [weightFiniteMeasure_mass S pt hw]
    rfl
  have hcoeff : ((weightFiniteMeasure S pt w).mass : ℝ≥0∞)⁻¹ ≤
      ENNReal.ofReal (gaugeDoublingConstant θ) * (gaugeContent θ E)⁻¹ := by
    rw [hmasscoe]
    exact inverse_mass_le_content_constant
      (ENNReal.ofReal_pos.mpr (gaugeDoublingConstant_pos θ)).ne'
      ENNReal.ofReal_ne_top hmassbound
  let μ := weightProbabilityMeasure S pt w
  refine ⟨μ, weightProbabilityMeasure_compl_eq_zero hE.measurableSet hw hmass hptE, ?_⟩
  intro i hi x r hr hri
  have hcube : ∀ k, (μ : Measure Plane) (dyadicCube i k) ≤
      (ENNReal.ofReal (gaugeDoublingConstant θ) * (gaugeContent θ E)⁻¹) *
        ENNReal.ofReal (realGauge θ (dyadicRadius i)) := by
    intro k
    refine (weightProbabilityMeasure_dyadicCube_le (d := thetaCapacity θ)
      hw hmass hptcube hbound hi k).trans ?_
    exact mul_le_mul_left hcoeff _
  have hball := measure_ball_le_of_cube_bound (x := x) hr hri hcube
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hball

end FalconerThetaGauge.GaugeFrostman
