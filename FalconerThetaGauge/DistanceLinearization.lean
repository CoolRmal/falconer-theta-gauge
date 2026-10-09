module

public import FalconerThetaGauge.MaskedMattilaGeometry

/-! # Exact quadratic control of the actual distance linearization in source §7.7 -/

@[expose] public section

noncomputable section

open scoped RealInnerProductSpace

namespace FalconerThetaGauge

def normLinearizationError (u h : Plane) : ℝ :=
  ‖u + h‖ - ‖u‖ - inner ℝ u h / ‖u‖

/-- The actual norm error has an exact quadratic numerator. -/
theorem normLinearizationError_eq {u : Plane} (hu : u ≠ 0) (h : Plane) :
    normLinearizationError u h =
      (‖h‖ ^ 2 - (‖u + h‖ - ‖u‖) ^ 2) / (2 * ‖u‖) := by
  have hn := norm_ne_zero_iff.mpr hu
  have hs := norm_add_sq_real u h
  unfold normLinearizationError
  field_simp
  nlinarith

theorem normLinearizationError_nonneg {u : Plane} (hu : u ≠ 0) (h : Plane) :
    0 ≤ normLinearizationError u h := by
  rw [normLinearizationError_eq hu]
  apply div_nonneg _ (by positivity)
  have hab : |‖u + h‖ - ‖u‖| ≤ ‖h‖ := by
    simpa using abs_norm_sub_norm_le (u + h) u
  have hs := pow_le_pow_left₀ (abs_nonneg _) hab 2
  rw [sq_abs] at hs
  linarith

/-- This global bound is stronger than the segment-Hessian estimate: no small
displacement condition is needed, only a nonzero expansion center. -/
theorem normLinearizationError_le {u : Plane} (hu : u ≠ 0) (h : Plane) :
    normLinearizationError u h ≤ ‖h‖ ^ 2 / (2 * ‖u‖) := by
  rw [normLinearizationError_eq hu]
  exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (‖u + h‖ - ‖u‖)])
    (by positivity)

def pairDistanceLinearizationError (a b x y : Plane) : ℝ :=
  normLinearizationError (a - b) ((x - a) - (y - b))

theorem pairDistance_linearization {a b : Plane} (hab : a ≠ b) (x y : Plane) :
    ‖x - y‖ = ‖a - b‖ +
      inner ℝ (pairDirection a b : Plane) ((x - a) - (y - b)) +
        pairDistanceLinearizationError a b x y := by
  have heq : a - b + ((x - a) - (y - b)) = x - y := by abel
  rw [coe_pairDirection_of_ne hab, real_inner_smul_left]
  unfold pairDistanceLinearizationError normLinearizationError
  rw [heq]
  ring

theorem pairDistanceLinearizationError_nonneg {a b : Plane} (hab : a ≠ b) (x y : Plane) :
    0 ≤ pairDistanceLinearizationError a b x y :=
  normLinearizationError_nonneg (sub_ne_zero.mpr hab) _

theorem pairDistanceLinearizationError_le {a b : Plane} (hab : a ≠ b) (x y : Plane) :
    pairDistanceLinearizationError a b x y ≤
      ‖(x - a) - (y - b)‖ ^ 2 / (2 * dist a b) := by
  simpa only [dist_eq_norm, pairDistanceLinearizationError] using
    normLinearizationError_le (sub_ne_zero.mpr hab)
    ((x - a) - (y - b))

end FalconerThetaGauge
