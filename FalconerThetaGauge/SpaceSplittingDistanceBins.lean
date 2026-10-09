module

public import FalconerThetaGauge.SpaceSplittingGeometry

/-! # Every actual far distance belongs to one of the literal source depth bins -/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- The finite source bin exists directly from the near/far and root diameter bounds. -/
theorem exists_spaceSplitting_distance_bin {a p : ℕ} {d : ℝ}
    (hroot : d ≤ 3 / 2 * dyadicRadius a)
    (hfar : 5 / 2 * dyadicRadius p < d) :
    ∃ n ∈ Finset.Ioo a (p + 12),
      4000 * dyadicRadius n < d ∧ d ≤ 8000 * dyadicRadius n := by
  have h11 : dyadicRadius (11 : ℕ) = 1 / 2048 := by
    norm_num [dyadicRadius, Real.rpow_neg, Real.rpow_natCast]
  have hex : ∃ n : ℕ, 4000 * dyadicRadius n < d := by
    refine ⟨p + 11, ?_⟩
    rw [dyadicRadius_add, h11]
    linarith [dyadicRadius_pos p]
  let n := Nat.find hex
  have hlow : 4000 * dyadicRadius n < d := Nat.find_spec hex
  have hnp : n ≤ p + 11 := by
    apply Nat.find_min'
    rw [dyadicRadius_add, h11]
    linarith [dyadicRadius_pos p]
  have han : a < n := by
    by_contra h
    have hrad := dyadicRadius_antitone (le_of_not_gt h)
    linarith [dyadicRadius_pos a]
  have hn : 0 < n := by omega
  have hprev : d ≤ 4000 * dyadicRadius (n - 1) := by
    exact le_of_not_gt (Nat.find_min hex (by omega : n - 1 < n))
  have hrad : dyadicRadius (n - 1) = 2 * dyadicRadius n := by
    have hstep := dyadicRadius_add (n - 1) 1
    have hn' : n - 1 + 1 = n := by omega
    rw [hn', show dyadicRadius 1 = 1 / 2 by
      norm_num [dyadicRadius, Real.rpow_neg, Real.rpow_natCast]] at hstep
    linarith
  exact ⟨n, Finset.mem_Ioo.2 ⟨han, by omega⟩, hlow, by rw [hrad] at hprev; linarith⟩

theorem exists_spaceSplitting_distance_bin_of_far {a p : ℕ}
    {A B : Fin 2 → ℤ} {R S : (Fin 2 → ℤ) × (Fin 2 → ℤ)} {x x' y y' : Plane}
    (hfar : ¬spaceSplittingNear p R S)
    (hx : x ∈ dyadicCube p R.1) (hx' : x' ∈ dyadicCube p S.1)
    (hy : y ∈ dyadicCube p R.2) (hy' : y' ∈ dyadicCube p S.2)
    (hxA : x ∈ dyadicCube a A) (hxA' : x' ∈ dyadicCube a A)
    (hyB : y ∈ dyadicCube a B) (hyB' : y' ∈ dyadicCube a B) :
    ∃ n ∈ Finset.Ioo a (p + 12),
      4000 * dyadicRadius n < max (dist x x') (dist y y') ∧
        max (dist x x') (dist y y') ≤ 8000 * dyadicRadius n := by
  apply exists_spaceSplitting_distance_bin _ (spaceSplittingFar_distance_gt hfar hx hx' hy hy')
  apply max_le
  · simpa only [dist_eq_norm] using norm_sub_le_of_mem_same_dyadicCube hxA hxA'
  · simpa only [dist_eq_norm] using norm_sub_le_of_mem_same_dyadicCube hyB hyB'

end FalconerThetaGauge
