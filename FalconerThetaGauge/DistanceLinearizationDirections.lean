module

public import FalconerThetaGauge.DistanceLinearizationCollision
public import Mathlib.Analysis.Normed.Module.Normalize

/-! # Actual direction motion inside a separated fine-cell pair -/

@[expose] public section

noncomputable section

open Set

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem norm_normalized_sub_le {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0) :
    ‖‖u‖⁻¹ • u - ‖v‖⁻¹ • v‖ ≤ 2 * ‖u - v‖ / ‖u‖ := by
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have heq : ‖u‖⁻¹ • u - ‖v‖⁻¹ • v =
      ‖u‖⁻¹ • (u - v) + (‖u‖⁻¹ * (‖v‖ - ‖u‖)) • (‖v‖⁻¹ • v) := by
    rw [smul_sub, smul_smul,
      show ‖u‖⁻¹ * (‖v‖ - ‖u‖) * ‖v‖⁻¹ = ‖u‖⁻¹ - ‖v‖⁻¹ by
        field_simp,
      sub_smul]
    abel
  rw [heq]
  calc
    _ ≤ ‖‖u‖⁻¹ • (u - v)‖ +
        ‖(‖u‖⁻¹ * (‖v‖ - ‖u‖)) • (‖v‖⁻¹ • v)‖ := norm_add_le _ _
    _ = ‖u‖⁻¹ * ‖u - v‖ + ‖u‖⁻¹ * |‖v‖ - ‖u‖| := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_mul, abs_of_pos (inv_pos.mpr hnu)]
      rw [show ‖‖v‖⁻¹ • v‖ = 1 from NormedSpace.norm_normalize hv]
      ring
    _ ≤ ‖u‖⁻¹ * ‖u - v‖ + ‖u‖⁻¹ * ‖u - v‖ := by
      gcongr
      simpa only [norm_sub_rev] using abs_norm_sub_norm_le v u
    _ = _ := by ring

theorem norm_pairDirection_sub_le {x y x' y' : Plane} (hxy : x ≠ y) (hxy' : x' ≠ y') :
    ‖(pairDirection x y : Plane) - (pairDirection x' y' : Plane)‖ ≤
      2 * ‖(x - y) - (x' - y')‖ / dist x y := by
  rw [coe_pairDirection_of_ne hxy, coe_pairDirection_of_ne hxy', dist_eq_norm]
  exact norm_normalized_sub_le (sub_ne_zero.mpr hxy) (sub_ne_zero.mpr hxy')

theorem norm_pair_displacement_sub_lt {p : ℕ} {P Q : Fin 2 → ℤ} {x y x' y' : Plane}
    (hx : x ∈ dyadicCube p P) (hy : y ∈ dyadicCube p Q)
    (hx' : x' ∈ dyadicCube p P) (hy' : y' ∈ dyadicCube p Q) :
    ‖(x - y) - (x' - y')‖ < 4 * dyadicRadius p := by
  have heq : (x - y) - (x' - y') = (x - x') - (y - y') := by abel
  rw [heq]
  exact (norm_sub_le _ _).trans_lt (by
    have hx₂ := norm_sub_lt_two_dyadicRadius hx hx'
    have hy₂ := norm_sub_lt_two_dyadicRadius hy hy'
    dsimp only [dyadicRadius] at *
    linarith)

/-- Any two actual pairs in a retained fine-cell pair have quantitatively close
directions. The source's coarse-cell separation supplies the denominator. -/
theorem norm_pairDirection_sub_cells_le {a p : ℕ} {A B P Q : Fin 2 → ℤ}
    (hsep : SeparatedDyadicCells a A B) (hP : dyadicCube p P ⊆ dyadicCube a A)
    (hQ : dyadicCube p Q ⊆ dyadicCube a B) {x y x' y' : Plane}
    (hx : x ∈ dyadicCube p P) (hy : y ∈ dyadicCube p Q)
    (hx' : x' ∈ dyadicCube p P) (hy' : y' ∈ dyadicCube p Q) :
    ‖(pairDirection x y : Plane) - (pairDirection x' y' : Plane)‖ ≤
      (2 / 125 : ℝ) * (2 : ℝ) ^ ((a : ℝ) - p) := by
  have hD := (dist_bounds_of_separatedDyadicCells hsep (hP hx) (hQ hy)).1
  have hD' := (dist_bounds_of_separatedDyadicCells hsep (hP hx') (hQ hy')).1
  have hxy : x ≠ y := dist_pos.mp (by linarith [dyadicRadius_pos a])
  have hxy' : x' ≠ y' := dist_pos.mp (by linarith [dyadicRadius_pos a])
  have hra := dyadicRadius_pos a
  have hrp := dyadicRadius_pos p
  calc
    _ ≤ 2 * ‖(x - y) - (x' - y')‖ / dist x y :=
      norm_pairDirection_sub_le hxy hxy'
    _ ≤ (2 * (4 * dyadicRadius p)) / (500 * dyadicRadius a) :=
      div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_left (norm_pair_displacement_sub_lt hx hy hx' hy').le
          (by norm_num)) (by positivity) hD
    _ = _ := by
      rw [show (2 * (4 * dyadicRadius p)) / (500 * dyadicRadius a) =
        (2 / 125 : ℝ) * (dyadicRadius p / dyadicRadius a) by ring,
        dyadicRadius, dyadicRadius, ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring

end FalconerThetaGauge
