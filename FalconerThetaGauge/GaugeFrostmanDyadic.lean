/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerThetaGauge.Statement
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Dyadic cubes in the plane

Adapted from `FalconerPacking.Dyadic` (original attribution preserved above),
`CoolRmal/falconer-packing` commit `70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/blob/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking/Dyadic.lean
This is the geometric cube hierarchy used in the finite gauge Frostman construction.  A dyadic square of generation `n` is a product of
half-open coordinate intervals of side `2⁻ⁿ`, indexed by integers.

* `mem_dyadicCube_iff` — membership is exactly the statement that the index is the floor index,
  so the generation-`n` cubes partition the plane;
* `dyadicCube_disjoint` — distinct cubes of one generation are disjoint;
* `dyadicCube_succ_subset` — each cube is contained in its parent, whose index is `k / 2`;
* `dist_le_of_mem_dyadicCube` — a generation-`n` cube has diameter at most `√2 / 2ⁿ`;
* `measurableSet_dyadicCube` — cubes are Borel.

This is the geometric hierarchy, not `Data.Dyadic`, which is an arithmetic number type.
-/

@[expose] public section

noncomputable section

open Set

namespace FalconerThetaGauge.GaugeFrostman

/-- The dyadic square of generation `n` with integer index `k`, half-open in each coordinate. -/
def dyadicCube (n : ℕ) (k : Fin 2 → ℤ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | ∀ i, (k i : ℝ) ≤ 2 ^ n * x i ∧ 2 ^ n * x i < (k i : ℝ) + 1}

/-- The index of the generation-`n` cube containing `x`. -/
def cubeIndex (n : ℕ) (x : EuclideanSpace ℝ (Fin 2)) : Fin 2 → ℤ := fun i ↦ ⌊(2 : ℝ) ^ n * x i⌋

theorem mem_dyadicCube_iff {n : ℕ} {k : Fin 2 → ℤ} {x : EuclideanSpace ℝ (Fin 2)} :
    x ∈ dyadicCube n k ↔ cubeIndex n x = k := by
  constructor
  · intro h
    funext i
    exact Int.floor_eq_iff.2 ⟨(h i).1, (h i).2⟩
  · intro h i
    have hi : ⌊(2 : ℝ) ^ n * x i⌋ = k i := congrFun h i
    rw [← hi]
    exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩

theorem mem_dyadicCube_cubeIndex (n : ℕ) (x : EuclideanSpace ℝ (Fin 2)) : x ∈ dyadicCube n (cubeIndex n x) :=
  mem_dyadicCube_iff.2 rfl

/-- Distinct cubes of the same generation are disjoint. -/
theorem dyadicCube_disjoint {n : ℕ} {k k' : Fin 2 → ℤ} (h : k ≠ k') :
    Disjoint (dyadicCube n k) (dyadicCube n k') := by
  refine Set.disjoint_left.2 fun x hx hx' ↦ h ?_
  rw [← mem_dyadicCube_iff.1 hx, mem_dyadicCube_iff.1 hx']

/-- The index of the parent cube is the index halved. -/
theorem cubeIndex_succ (n : ℕ) (x : EuclideanSpace ℝ (Fin 2)) :
    cubeIndex n x = fun i ↦ cubeIndex (n + 1) x i / 2 := by
  funext i
  have h : (2 : ℝ) ^ n * x i = ((2 : ℝ) ^ (n + 1) * x i) / (2 : ℕ) := by
    push_cast
    ring
  rw [cubeIndex, cubeIndex, h, Int.floor_div_natCast]
  norm_num

/-- Each cube is contained in its parent. -/
theorem dyadicCube_succ_subset (n : ℕ) (x : EuclideanSpace ℝ (Fin 2)) :
    dyadicCube (n + 1) (cubeIndex (n + 1) x) ⊆ dyadicCube n (cubeIndex n x) := by
  intro y hy
  have hy' : cubeIndex (n + 1) y = cubeIndex (n + 1) x := mem_dyadicCube_iff.1 hy
  refine mem_dyadicCube_iff.2 ?_
  rw [cubeIndex_succ n y, cubeIndex_succ n x, hy']

/-- A generation-`n` cube has diameter at most `√2 / 2ⁿ`. -/
theorem dist_le_of_mem_dyadicCube {n : ℕ} {k : Fin 2 → ℤ} {x y : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ dyadicCube n k) (hy : y ∈ dyadicCube n k) :
    dist x y ≤ Real.sqrt 2 / (2 : ℝ) ^ n := by
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hcoord : ∀ i, |x i - y i| < 1 / (2 : ℝ) ^ n := by
    intro i
    have h₁ := hx i
    have h₂ := hy i
    have hd : |(2 : ℝ) ^ n * (x i - y i)| < 1 := by
      rw [abs_lt]
      constructor <;> nlinarith [h₁.1, h₁.2, h₂.1, h₂.2]
    rw [abs_mul, abs_of_pos hpow] at hd
    rw [lt_div_iff₀ hpow, mul_comm]
    exact hd
  rw [EuclideanSpace.dist_eq]
  have hsum : ∑ i, dist (x i) (y i) ^ 2 ≤ 2 * (1 / (2 : ℝ) ^ n) ^ 2 := by
    have hterm : ∀ i : Fin 2, dist (x i) (y i) ^ 2 ≤ (1 / (2 : ℝ) ^ n) ^ 2 := by
      intro i
      rw [Real.dist_eq]
      exact pow_le_pow_left₀ (abs_nonneg _) (hcoord i).le 2
    calc ∑ i, dist (x i) (y i) ^ 2 ≤ ∑ _i : Fin 2, (1 / (2 : ℝ) ^ n) ^ 2 :=
          Finset.sum_le_sum fun i _ ↦ hterm i
      _ = 2 * (1 / (2 : ℝ) ^ n) ^ 2 := by
          simp [Finset.sum_const]
  calc Real.sqrt (∑ i, dist (x i) (y i) ^ 2)
      ≤ Real.sqrt (2 * (1 / (2 : ℝ) ^ n) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 2 / (2 : ℝ) ^ n := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity), mul_one_div]

theorem measurableSet_dyadicCube (n : ℕ) (k : Fin 2 → ℤ) :
    MeasurableSet (dyadicCube n k) := by
  have hset : dyadicCube n k
      = ⋂ i, (fun x : EuclideanSpace ℝ (Fin 2) ↦ (2 : ℝ) ^ n * x i) ⁻¹' Ico ((k i : ℝ)) ((k i : ℝ) + 1) := by
    ext x
    simp [dyadicCube, Set.mem_Ico]
  rw [hset]
  refine MeasurableSet.iInter fun i ↦ ?_
  have hmeas : Measurable fun x : EuclideanSpace ℝ (Fin 2) ↦ (2 : ℝ) ^ n * x i := by fun_prop
  exact hmeas measurableSet_Ico

section Counting

/-- Coordinates are 1-Lipschitz for the Euclidean distance. -/
theorem abs_sub_coord_le_dist (x y : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) : |x i - y i| ≤ dist x y := by
  rw [EuclideanSpace.dist_eq]
  have hle : dist (x i) (y i) ^ 2 ≤ ∑ j, dist (x j) (y j) ^ 2 :=
    Finset.single_le_sum (f := fun j ↦ dist (x j) (y j) ^ 2)
      (fun j _ ↦ by positivity) (Finset.mem_univ i)
  have h0 : (0 : ℝ) ≤ ∑ j, dist (x j) (y j) ^ 2 :=
    Finset.sum_nonneg fun j _ ↦ by positivity
  rw [← Real.dist_eq]
  calc dist (x i) (y i) = Real.sqrt (dist (x i) (y i) ^ 2) := by
        rw [Real.sqrt_sq dist_nonneg]
    _ ≤ Real.sqrt (∑ j, dist (x j) (y j) ^ 2) := Real.sqrt_le_sqrt hle

/-- **A small ball meets at most four cubes.**  If the ball has radius at most `2⁻ⁿ⁻¹`, then in
each coordinate the cube index of its points is the lower index determined by the ball, or its
successor. -/
theorem cubeIndex_eq_lower_or_succ (n : ℕ) (x : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (_hr : 0 < r)
    (hrn : r ≤ (2 : ℝ) ^ (-((n : ℝ) + 1))) :
    ∀ y ∈ Metric.ball x r, ∀ i,
      cubeIndex n y i = ⌊(2 : ℝ) ^ n * (x i - r)⌋ ∨
        cubeIndex n y i = ⌊(2 : ℝ) ^ n * (x i - r)⌋ + 1 := by
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have h2r : (2 : ℝ) ^ n * (2 * r) ≤ 1 := by
    have hval : (2 : ℝ) ^ n * (2 * (2 : ℝ) ^ (-((n : ℝ) + 1))) = 1 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        Real.rpow_natCast, Real.rpow_one]
      field_simp
    calc (2 : ℝ) ^ n * (2 * r)
        ≤ (2 : ℝ) ^ n * (2 * (2 : ℝ) ^ (-((n : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrn (by norm_num)) hpow.le
      _ = 1 := hval
  have hsplit : (2 : ℝ) ^ n * (2 * r) = 2 * ((2 : ℝ) ^ n * r) := by ring
  intro y hy i
  have hdist : |y i - x i| < r := by
    refine lt_of_le_of_lt ?_ (Metric.mem_ball.1 hy)
    simpa [abs_sub_comm] using abs_sub_coord_le_dist y x i
  have habs := abs_lt.1 hdist
  have hlow : (2 : ℝ) ^ n * (x i - r) ≤ 2 ^ n * y i :=
    mul_le_mul_of_nonneg_left (by linarith [habs.1]) hpow.le
  have hmul : (2 : ℝ) ^ n * y i < 2 ^ n * (x i + r) :=
    mul_lt_mul_of_pos_left (by linarith [habs.2]) hpow
  have hhigh : (2 : ℝ) ^ n * y i < 2 ^ n * (x i - r) + 2 := by
    have hexp : (2 : ℝ) ^ n * (x i + r) = 2 ^ n * (x i - r) + 2 * ((2 : ℝ) ^ n * r) := by ring
    rw [hexp] at hmul
    linarith [h2r, hsplit]
  have hfloor_low : ⌊(2 : ℝ) ^ n * (x i - r)⌋ ≤ ⌊(2 : ℝ) ^ n * y i⌋ := Int.floor_le_floor hlow
  have hfloor_high : ⌊(2 : ℝ) ^ n * y i⌋ ≤ ⌊(2 : ℝ) ^ n * (x i - r)⌋ + 1 := by
    have hlt : (2 : ℝ) ^ n * y i < ((⌊(2 : ℝ) ^ n * (x i - r)⌋ : ℤ) : ℝ) + 2 := by
      have := Int.lt_floor_add_one ((2 : ℝ) ^ n * (x i - r))
      linarith [hhigh]
    have hf : ⌊(2 : ℝ) ^ n * y i⌋ < ⌊(2 : ℝ) ^ n * (x i - r)⌋ + 2 := by
      refine Int.floor_lt.2 ?_
      push_cast
      linarith [hlt]
    omega
  have hidx : cubeIndex n y i = ⌊(2 : ℝ) ^ n * y i⌋ := rfl
  rw [hidx]
  rcases eq_or_lt_of_le hfloor_low with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by omega)

/-- Existential form of `cubeIndex_eq_lower_or_succ`. -/
theorem exists_cubeIndex_pair (n : ℕ) (x : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r)
    (hrn : r ≤ (2 : ℝ) ^ (-((n : ℝ) + 1))) :
    ∃ k : Fin 2 → ℤ, ∀ y ∈ Metric.ball x r, ∀ i,
      cubeIndex n y i = k i ∨ cubeIndex n y i = k i + 1 :=
  ⟨fun i ↦ ⌊(2 : ℝ) ^ n * (x i - r)⌋, cubeIndex_eq_lower_or_succ n x hr hrn⟩

end Counting

section Ancestors

/-- The index of the generation-`n` ancestor, `m` levels up. -/
def ancestor (m : ℕ) (k : Fin 2 → ℤ) : Fin 2 → ℤ := fun i ↦ k i / 2 ^ m

@[simp] theorem ancestor_zero (k : Fin 2 → ℤ) : ancestor 0 k = k := by
  funext i
  simp [ancestor]

theorem ancestor_succ (m : ℕ) (k : Fin 2 → ℤ) :
    ancestor (m + 1) k = ancestor m (fun i ↦ k i / 2) := by
  funext i
  simp only [ancestor]
  rw [Int.ediv_ediv_of_nonneg (by norm_num : (0 : ℤ) ≤ 2), pow_succ, mul_comm]

/-- Each cube sits inside the cube of the previous generation with halved index. -/
theorem dyadicCube_subset_parent (n : ℕ) (k : Fin 2 → ℤ) :
    dyadicCube (n + 1) k ⊆ dyadicCube n (fun i ↦ k i / 2) := by
  intro y hy
  have hy' : cubeIndex (n + 1) y = k := mem_dyadicCube_iff.1 hy
  refine mem_dyadicCube_iff.2 ?_
  rw [cubeIndex_succ n y, hy']

/-- Iterating the parent map: each cube sits inside its `m`-th ancestor. -/
theorem dyadicCube_subset_ancestor (j m : ℕ) (k : Fin 2 → ℤ) :
    dyadicCube (j + m) k ⊆ dyadicCube j (ancestor m k) := by
  induction m generalizing k with
  | zero => simp
  | succ m ih =>
      intro y hy
      have hy' : y ∈ dyadicCube (j + m + 1) k := by
        rwa [show j + (m + 1) = j + m + 1 by ring] at hy
      have hstep := dyadicCube_subset_parent (j + m) k hy'
      have := ih (fun i ↦ k i / 2) hstep
      rwa [← ancestor_succ] at this

/-- Ancestors compose. -/
theorem ancestor_ancestor (a b : ℕ) (k : Fin 2 → ℤ) :
    ancestor a (ancestor b k) = ancestor (a + b) k := by
  funext i
  simp only [ancestor]
  rw [Int.ediv_ediv_of_nonneg (by positivity), ← pow_add, add_comm b a]

end Ancestors

end FalconerThetaGauge.GaugeFrostman
