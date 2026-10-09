module

public import FalconerThetaGauge.SpaceSplittingRadialDecay

/-! # The actual pair of stationary orders in the source radial-kernel bound -/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

theorem stationary_orders_natAbs_le (j j' : ℕ) :
    (1 - (j : ℤ) - j').natAbs ≤ j + j' + 1 := by
  apply (Nat.cast_le (α := ℤ)).1
  rw [Int.natCast_natAbs, abs_le]
  push_cast
  constructor <;> omega

theorem stationary_orders_abs_le (j j' : ℕ) :
    |((1 - (j : ℤ) - j' : ℤ) : ℝ)| + 1 ≤ (j : ℝ) + j' + 2 := by
  have h := (Nat.cast_le (α := ℝ)).2 (stationary_orders_natAbs_le j j')
  rw [Nat.cast_natAbs, Int.cast_abs] at h
  push_cast at h ⊢
  linarith

theorem spaceSplittingRadialBound_orders_le (v j j' : ℕ) :
    spaceSplittingRadialBound v (1 - (j : ℤ) - j') ≤
      (4 : ℝ) ^ (j + j' + 1) * (2 : ℝ) ^ ((v : ℝ) * (1 - (j : ℝ) - j')) := by
  unfold spaceSplittingRadialBound
  have heq : (((2 : ℝ) ^ v) ^ (1 - (j : ℤ) - j')) =
      (2 : ℝ) ^ ((v : ℝ) * (1 - (j : ℝ) - j')) := by
    rw [← Real.rpow_intCast,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast
    rfl
  rw [heq]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num) (stationary_orders_natAbs_le j j')) (by positivity)

/-- The twice-integrated actual moment has exactly the source stationary-order envelope. -/
theorem norm_spaceSplittingRadialMoment_orders_le {K v : ℕ} (hK : 2 ≤ K)
    (j j' : ℕ) (δ : ℝ) :
    ‖spaceSplittingRadialMoment K v (1 - (j : ℤ) - j') δ‖ ≤
      12544 * ((j : ℝ) + j' + 2) ^ 2 * (4 : ℝ) ^ (j + j' + 1) *
        (2 : ℝ) ^ ((v : ℝ) * (1 - (j : ℝ) - j')) /
          (1 + (2 : ℝ) ^ v * |δ|) ^ 2 := by
  apply (norm_spaceSplittingRadialMoment_le_kernel hK (1 - (j : ℤ) - j') δ).trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have hsq := pow_le_pow_left₀ (by positivity)
    (stationary_orders_abs_le j j') 2
  have h := mul_le_mul (spaceSplittingRadialBound_orders_le v j j') hsq (by positivity)
    (by positivity)
  convert mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 12544) using 1 <;> ring

end FalconerThetaGauge
