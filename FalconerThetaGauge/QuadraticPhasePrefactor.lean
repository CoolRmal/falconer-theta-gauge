module

public import FalconerThetaGauge.QuadraticPhaseFourier

/-!
# The principal-branch phase of the quadratic Gaussian prefactor
-/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

theorem quadraticPhasePrefactor_eq {Λ : ℝ} (hΛ : 0 < Λ) :
    quadraticPhasePrefactor Λ = (Real.sqrt (2 * Real.pi / Λ) : ℂ) *
      Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) := by
  let r : ℝ := 2 * Real.pi / Λ
  have hr : 0 < r := by dsimp only [r]; positivity
  have hbase : (Real.pi : ℂ) / (-((Λ / 2 : ℝ) : ℂ) * Complex.I) =
      (r : ℂ) * Complex.I := by
    dsimp only [r]
    push_cast
    field_simp
    simp only [Complex.I_sq]
    ring
  have hreal : Complex.exp ((Real.log r : ℂ) * (1 / 2 : ℂ)) = (Real.sqrt r : ℂ) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [quadraticPhasePrefactor, hbase,
    Complex.cpow_def_of_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne')
      Complex.I_ne_zero), Complex.log_ofReal_mul hr Complex.I_ne_zero, Complex.log_I]
  have hexp : ((Real.log r : ℂ) + (Real.pi : ℂ) / 2 * Complex.I) * (1 / 2 : ℂ) =
      (Real.log r : ℂ) * (1 / 2 : ℂ) + (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hexp, Complex.exp_add, hreal]

theorem norm_quadraticPhasePrefactor_half_le {Λ : ℝ} (hΛ : 0 < Λ) :
    ‖quadraticPhasePrefactor Λ‖ / 2 ≤ Real.sqrt (2 / Λ) := by
  rw [norm_quadraticPhasePrefactor hΛ]
  have harg : 2 * Real.pi / Λ ≤ 4 * (2 / Λ) := by
    calc
      _ ≤ (4 * 2) / Λ :=
        (div_le_div_iff_of_pos_right hΛ).mpr (by linarith [Real.pi_le_four])
      _ = _ := by ring
  have h := Real.sqrt_le_sqrt harg
  have hs4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hs4] at h
  linarith

end FalconerThetaGauge
