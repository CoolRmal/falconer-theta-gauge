module

public import FalconerThetaGauge.DistanceLinearization

/-! # Exact source linearization error on the actual separated fine dyadic cells -/

@[expose] public section

noncomputable section

open Set

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem abs_sub_dyadicCellCenter_coord_le_half {p : ℕ} {P : Fin 2 → ℤ} {x : Plane}
    (hx : x ∈ dyadicCube p P) (i : Fin 2) :
    |x i - dyadicCellCenter p P i| ≤ dyadicRadius p / 2 := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hxi := hx i
  have hhalf : |(2 : ℝ) ^ p * x i - ((P i : ℝ) + 1 / 2)| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have heq : (2 : ℝ) ^ p * (x i - dyadicCellCenter p P i) =
      (2 : ℝ) ^ p * x i - ((P i : ℝ) + 1 / 2) := by
    change (2 : ℝ) ^ p * (x i - (((P i : ℝ) + 1 / 2) / (2 : ℝ) ^ p)) = _
    field_simp
  rw [← heq, abs_mul, abs_of_pos hp] at hhalf
  calc
    _ ≤ (1 / 2 : ℝ) / (2 : ℝ) ^ p := (le_div_iff₀ hp).mpr (by linarith)
    _ = _ := by
      rw [dyadicRadius, Real.rpow_neg (by norm_num), Real.rpow_natCast]
      ring

theorem pair_cell_displacement_sq_le {p : ℕ} {P Q : Fin 2 → ℤ} {x y : Plane}
    (hx : x ∈ dyadicCube p P) (hy : y ∈ dyadicCube p Q) :
    ‖(x - dyadicCellCenter p P) - (y - dyadicCellCenter p Q)‖ ^ 2 ≤
      2 * dyadicRadius p ^ 2 := by
  have hcoord (i : Fin 2) :
      |((x - dyadicCellCenter p P) - (y - dyadicCellCenter p Q)) i| ≤ dyadicRadius p := by
    change |(x i - dyadicCellCenter p P i) - (y i - dyadicCellCenter p Q i)| ≤ _
    have hx' := abs_sub_dyadicCellCenter_coord_le_half hx i
    have hy' := abs_sub_dyadicCellCenter_coord_le_half hy i
    exact (abs_sub _ _).trans (by linarith)
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _i : Fin 2, dyadicRadius p ^ 2 := Finset.sum_le_sum fun i hi ↦ by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hcoord i) 2
    _ = _ := by simp

theorem dyadicRadius_square_div_radius (p a : ℕ) :
    dyadicRadius p ^ 2 / dyadicRadius a = (2 : ℝ) ^ ((a : ℝ) - 2 * p) := by
  rw [dyadicRadius, dyadicRadius, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  norm_num only [Nat.cast_ofNat]
  congr 1
  ring

/-- The literal source bound `|E| ≤ 2⁻ᵗ/K`, with `K=1000`, follows from the
exact quadratic identity and the actual half-cell coordinate bounds. -/
theorem pairDistanceLinearizationError_cells_le {a p t : ℕ} {A B P Q : Fin 2 → ℤ}
    (hsep : SeparatedDyadicCells a A B) (hP : dyadicCube p P ⊆ dyadicCube a A)
    (hQ : dyadicCube p Q ⊆ dyadicCube a B) (hdepth : a + t < 2 * p)
    {x y : Plane} (hx : x ∈ dyadicCube p P) (hy : y ∈ dyadicCube p Q) :
    |pairDistanceLinearizationError (dyadicCellCenter p P) (dyadicCellCenter p Q) x y| ≤
      (2 : ℝ) ^ (-(t : ℝ)) / 1000 := by
  have hD := (dist_bounds_of_separatedDyadicCells hsep
    (hP (dyadicCellCenter_mem_dyadicCube p P)) (hQ (dyadicCellCenter_mem_dyadicCube p Q))).1
  have hr₀ := dyadicRadius_pos a
  have hcenters : dyadicCellCenter p P ≠ dyadicCellCenter p Q := by
    apply dist_pos.mp
    linarith
  rw [abs_of_nonneg (pairDistanceLinearizationError_nonneg hcenters x y)]
  calc
    _ ≤ ‖(x - dyadicCellCenter p P) - (y - dyadicCellCenter p Q)‖ ^ 2 /
        (2 * dist (dyadicCellCenter p P) (dyadicCellCenter p Q)) :=
      pairDistanceLinearizationError_le hcenters x y
    _ ≤ (2 * dyadicRadius p ^ 2) / (2 * (500 * dyadicRadius a)) :=
      div_le_div₀ (by positivity) (pair_cell_displacement_sq_le hx hy)
        (by positivity) (by linarith)
    _ = (1 / 500 : ℝ) * (2 : ℝ) ^ ((a : ℝ) - 2 * p) := by
      rw [show (2 * dyadicRadius p ^ 2) / (2 * (500 * dyadicRadius a)) =
        (1 / 500 : ℝ) * (dyadicRadius p ^ 2 / dyadicRadius a) by ring,
        dyadicRadius_square_div_radius]
    _ ≤ (1 / 500 : ℝ) * (2 : ℝ) ^ (-(t : ℝ) - 1) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have h' : (a : ℝ) + t + 1 ≤ 2 * p := by exact_mod_cast hdepth
      linarith
    _ = _ := by
      rw [Real.rpow_sub (by norm_num), Real.rpow_one]
      ring

end FalconerThetaGauge
