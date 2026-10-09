/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.DirectionalTestsFilter
public import Mathlib.Algebra.BigOperators.Fin

/-! # Padding concrete piece tests to the common per-pin slot count -/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset
open scoped Classical

namespace FalconerThetaGauge

def FiniteDirectionalFilter.paddedBadTest {N : ℕ} {E : ℝ}
    (F : FiniteDirectionalFilter N E) (j : Fin (N ^ 2 + 1)) : Set (Plane × UnitCircle) :=
  if h : j.val < F.testCount then F.badTest ⟨j.val, h⟩ else ∅

def FiniteDirectionalFilter.paddedMaskTest {N : ℕ} {E : ℝ}
    (F : FiniteDirectionalFilter N E) (j : Fin (N ^ 2 + 1)) : Plane → UnitCircle → ℝ :=
  if h : j.val < F.testCount then F.maskTest ⟨j.val, h⟩ else fun _ _ => 1

theorem FiniteDirectionalFilter.paddedBadTest_measurable {N : ℕ} {E : ℝ}
    (F : FiniteDirectionalFilter N E) (j : Fin (N ^ 2 + 1)) :
    MeasurableSet (F.paddedBadTest j) := by
  unfold paddedBadTest
  split
  · exact F.badTest_measurable _
  · exact MeasurableSet.empty

theorem FiniteDirectionalFilter.paddedBadTest_symmetric {N : ℕ} {E : ℝ}
    (F : FiniteDirectionalFilter N E) (j : Fin (N ^ 2 + 1)) :
    IsSymmetricBadDirections (F.paddedBadTest j) := by
  unfold paddedBadTest
  split
  · exact F.badTest_symmetric _
  · intro x w
    simp

theorem FiniteDirectionalFilter.paddedBadTest_short {N : ℕ} {E : ℝ}
    (F : FiniteDirectionalFilter N E) (j : Fin (N ^ 2 + 1)) (x : Plane) :
    circleArcLength (badDirectionsAt (F.paddedBadTest j) x) ≤
      ENNReal.ofReal (2 * Real.pi * (2 : ℝ) ^ (-2 * E)) := by
  unfold paddedBadTest
  split
  · exact F.badTest_short _ x
  · simp [badDirectionsAt]

theorem FiniteDirectionalFilter.paddedMaskTest_measurable {N : ℕ} {E : ℝ}
    (F : FiniteDirectionalFilter N E) (j : Fin (N ^ 2 + 1)) :
    Measurable (Function.uncurry (F.paddedMaskTest j)) := by
  unfold paddedMaskTest
  split
  · exact F.maskTest_measurable _
  · exact measurable_const

theorem FiniteDirectionalFilter.paddedMaskTest_range {N : ℕ} {E : ℝ}
    (F : FiniteDirectionalFilter N E) (j : Fin (N ^ 2 + 1)) (x : Plane) (w : UnitCircle) :
    F.paddedMaskTest j x w ∈ Set.Icc 0 1 := by
  unfold paddedMaskTest
  split
  · exact F.maskTest_range _ x w
  · simp

theorem FiniteDirectionalFilter.paddedMaskTest_passing {N : ℕ} {E : ℝ}
    (F : FiniteDirectionalFilter N E) (j : Fin (N ^ 2 + 1)) {x : Plane}
    (hx : x ∈ F.carrier) {w : UnitCircle} (hw : (x, w) ∉ F.paddedBadTest j) :
    F.paddedMaskTest j x w = 1 := by
  by_cases h : j.val < F.testCount
  · simp only [paddedMaskTest, paddedBadTest, dite_eq_left h] at *
    exact F.maskTest_passing _ x hx w hw
  · simp [paddedMaskTest, h]

/-- Neutral padding preserves the actual product of all masks on a piece. -/
theorem FiniteDirectionalFilter.prod_paddedMaskTest {N : ℕ} {E : ℝ}
    (F : FiniteDirectionalFilter N E) (x : Plane) (w : UnitCircle) :
    (∏ j : Fin (N ^ 2 + 1), F.paddedMaskTest j x w) = ∏ i, F.maskTest i x w := by
  classical
  have hused : ∀ j : Fin (N ^ 2 + 1), F.paddedMaskTest j x w ≠ 1 → j.val < F.testCount := by
    intro j hne
    by_contra h
    exact hne (by simp [paddedMaskTest, h])
  apply Finset.prod_bij_ne_one (fun j _ hne => ⟨j.val, hused j hne⟩)
  · intro j hj hne
    exact mem_univ _
  · intro j hj hne k hk hne' heq
    exact Fin.ext (congrArg (fun z : Fin F.testCount => z.val) heq)
  · intro i hi hne
    refine ⟨⟨i.val, lt_of_lt_of_le i.isLt F.testCount_le⟩, mem_univ _, ?_, ?_⟩
    · simpa [paddedMaskTest, i.isLt] using hne
    · exact Fin.ext rfl
  · intro j hj hne
    simp [paddedMaskTest, hused j hne]

end FalconerThetaGauge
