module

public import FalconerThetaGauge.SpaceSplittingDistanceCover

/-! # The genuine far-cell geometry splits into the two Case A orientations and Case B -/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem spaceSplittingFar_not_comparable_cases {p : ℕ}
    {R S : (Fin 2 → ℤ) × (Fin 2 → ℤ)} {x x' y y' : Plane}
    (hfar : ¬spaceSplittingNear p R S)
    (hx : x ∈ dyadicCube p R.1) (hx' : x' ∈ dyadicCube p S.1)
    (hy : y ∈ dyadicCube p R.2) (hy' : y' ∈ dyadicCube p S.2)
    (hcase : ¬max (dist x x') (dist y y') ≤ 2 * min (dist x x') (dist y y')) :
    (5 / 4 * dyadicRadius p ≤ dist x x' ∧ 2 * dist y y' < dist x x') ∨
      (5 / 4 * dyadicRadius p ≤ dist y y' ∧ 2 * dist x x' < dist y y') := by
  have hm := spaceSplittingFar_distance_gt hfar hx hx' hy hy'
  rcases le_total (dist y y') (dist x x') with hd | hd
  · simp only [max_eq_left hd, min_eq_right hd] at hm hcase
    exact Or.inl ⟨by linarith [dyadicRadius_pos p], lt_of_not_ge hcase⟩
  · simp only [max_eq_right hd, min_eq_left hd] at hm hcase
    exact Or.inr ⟨by linarith [dyadicRadius_pos p], lt_of_not_ge hcase⟩

theorem spaceSplittingFar_mem_comparable_iff {p : ℕ}
    {R S : (Fin 2 → ℤ) × (Fin 2 → ℤ)} {x x' y y' : Plane}
    (hfar : ¬spaceSplittingNear p R S)
    (hx : x ∈ dyadicCube p R.1) (hx' : x' ∈ dyadicCube p S.1)
    (hy : y ∈ dyadicCube p R.2) (hy' : y' ∈ dyadicCube p S.2) :
    ((x, x'), (y, y')) ∈ spaceSplittingFarComparableSet p ↔
      max (dist x x') (dist y y') ≤ 2 * min (dist x x') (dist y y') :=
  ⟨fun hh ↦ hh.2, fun hh ↦ ⟨spaceSplittingFar_distance_gt hfar hx hx' hy hy', hh⟩⟩

end FalconerThetaGauge
