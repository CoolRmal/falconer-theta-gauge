module

public import FalconerThetaGauge.SpaceSplittingFarKernel

/-! # Finiteness follows from the actual far comparable distance lower bound -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerThetaGauge

open GaugeFrostman

theorem spaceSplittingFarWeightedKernel_ne_top (p v : ℕ) (Z₁ Z₂ : Set (Plane × Plane))
    (q : (Plane × Plane) × (Plane × Plane)) :
    spaceSplittingFarWeightedKernel p v Z₁ Z₂ q ≠ ∞ := by
  classical
  by_cases hq : q ∈ spaceSplittingFarComparableSet p
  · have hx : 0 < dist q.1.1 q.1.2 := by
      have hh := min_le_left (dist q.1.1 q.1.2) (dist q.2.1 q.2.2)
      have hr := dyadicRadius_pos p
      have h₁ := hq.1
      have h₂ := hq.2
      linarith
    have hy : 0 < dist q.2.1 q.2.2 := by
      have hh := min_le_right (dist q.1.1 q.1.2) (dist q.2.1 q.2.2)
      have hr := dyadicRadius_pos p
      have h₁ := hq.1
      have h₂ := hq.2
      linarith
    rw [spaceSplittingFarWeightedKernel, indicator_of_mem hq,
      spaceSplittingWeightedKernel_eq_ofReal hx hy]
    exact ENNReal.ofReal_ne_top
  · rw [spaceSplittingFarWeightedKernel, indicator_of_notMem hq]
    exact ENNReal.zero_ne_top

theorem spaceSplittingFarWeightedKernel_toReal (p v : ℕ) (Z₁ Z₂ : Set (Plane × Plane))
    (q : (Plane × Plane) × (Plane × Plane)) :
    (spaceSplittingFarWeightedKernel p v Z₁ Z₂ q).toReal =
      (spaceSplittingFarComparableSet p).indicator
        (fun z ↦ (spaceSplittingWeightedKernel ((2 : ℝ) ^ (-(v : ℝ))) Z₁ Z₂ z).toReal) q := by
  classical
  by_cases hq : q ∈ spaceSplittingFarComparableSet p
  · simp only [spaceSplittingFarWeightedKernel, indicator_of_mem hq]
  · simp only [spaceSplittingFarWeightedKernel, indicator_of_notMem hq, ENNReal.toReal_zero]

end FalconerThetaGauge
