module

public import FalconerThetaGauge.SpaceSplittingCircleRemainder
public import FalconerThetaGauge.SpaceSplittingOppositeSeries

/-! # Exact phases and radial powers of the actual stationary product -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FalconerThetaGauge

theorem spaceSplitting_stationary_prefactor {r dx dy : ℝ}
    (hr : 0 < r) (hx : 0 < dx) (hy : 0 < dy) :
    Real.sqrt (2 * Real.pi / (r * dx)) * Real.sqrt (2 * Real.pi / (r * dy)) * r =
      2 * Real.pi / Real.sqrt (dx * dy) := by
  rw [Real.sqrt_div (by positivity), Real.sqrt_div (by positivity),
    Real.sqrt_mul hr.le, Real.sqrt_mul hr.le, Real.sqrt_mul hx.le]
  have hs : Real.sqrt r ≠ 0 := (Real.sqrt_pos.2 hr).ne'
  have hsx : Real.sqrt dx ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have hsy : Real.sqrt dy ≠ 0 := (Real.sqrt_pos.2 hy).ne'
  field_simp
  nlinarith [Real.sq_sqrt hr.le, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]

theorem spaceSplitting_stationary_phase_opposite (r dx dy : ℝ) :
    Complex.exp (-((r * dx - Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((r * dy - Real.pi / 4 : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-((r * (dx - dy) : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem spaceSplitting_stationary_phase_equal_positive (r dx dy : ℝ) :
    Complex.exp (-((r * dx - Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
        Complex.exp (-((r * dy - Real.pi / 4 : ℝ) : ℂ) * Complex.I) =
      Complex.I * Complex.exp (-((r * (dx + dy) : ℝ) : ℂ) * Complex.I) := by
  calc
    _ = Complex.exp ((Real.pi : ℂ) / 2 * Complex.I) *
        Complex.exp (-((r * (dx + dy) : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    _ = _ := by rw [Complex.exp_pi_div_two_mul_I]

theorem spaceSplitting_stationary_phase_equal_negative (r dx dy : ℝ) :
    Complex.exp (((r * dx - Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((r * dy - Real.pi / 4 : ℝ) : ℂ) * Complex.I) =
      -Complex.I * Complex.exp (-((r * -(dx + dy) : ℝ) : ℂ) * Complex.I) := by
  have he : Complex.exp (-(Real.pi / 2 : ℝ) * Complex.I) = -Complex.I := by
    rw [neg_mul, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.exp_neg,
      Complex.exp_pi_div_two_mul_I]
    simp
  rw [← Complex.exp_add, ← he, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem spaceSplitting_stationary_radial_power {r dx dy : ℝ}
    (hr : r ≠ 0) (j k : ℕ) :
    (r : ℂ) * ((r * dx : ℝ) : ℂ)⁻¹ ^ j * ((r * dy : ℝ) : ℂ)⁻¹ ^ k =
      ((r ^ (1 - (j : ℤ) - k) : ℝ) : ℂ) / (dx : ℂ) ^ j / (dy : ℂ) ^ k := by
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  rw [Complex.ofReal_zpow, zpow_sub₀ hrc, zpow_sub₀ hrc]
  simp only [zpow_natCast, zpow_one, Complex.ofReal_mul, mul_inv_rev, mul_pow, inv_pow]
  ring

end FalconerThetaGauge
