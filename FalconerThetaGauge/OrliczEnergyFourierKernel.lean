module

public import FalconerThetaGauge.GaugeLogEnergy
public import FalconerThetaGauge.OrliczEnergyKernel
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The extended scalar kernel bound

The nonnegative extended series retains the infinite diagonal rather than
relying on the real `tsum` convention for a divergent series. At positive
radii it agrees with the convergent real kernel proved earlier.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace FalconerThetaGauge

/-- The extended nonnegative Gaussian series, including its value on the diagonal. -/
def ennDyadicGaussianKernel (γ r : ℝ) : ℝ≥0∞ := ∑' n, ENNReal.ofReal (dyadicGaussianTerm γ r n)

theorem ennDyadicGaussianKernel_eq_ofReal (γ r : ℝ) (hγ : 0 ≤ γ) (hr : 0 < r) :
    ennDyadicGaussianKernel γ r = ENNReal.ofReal (dyadicGaussianKernel γ r) :=
  (ENNReal.ofReal_tsum_of_nonneg (dyadicGaussianTerm_nonneg γ r)
    (summable_dyadicGaussianTerm γ r hγ hr)).symm

/-- A finite constant covering both small and large spatial radii. -/
def dyadicGaussianEnergyConstant (γ : ℝ) : ℝ :=
  dyadicGaussianBoundConstant γ + dyadicGaussianKernel γ 1

theorem dyadicGaussianEnergyConstant_pos (γ : ℝ) : 0 < dyadicGaussianEnergyConstant γ :=
  add_pos_of_pos_of_nonneg (dyadicGaussianBoundConstant_pos γ) (dyadicGaussianKernel_nonneg γ 1)

theorem ennDyadicGaussianKernel_le (γ r : ℝ) (hγ : 0 ≤ γ) (hr : 0 ≤ r) :
    ennDyadicGaussianKernel γ r ≤
      ENNReal.ofReal (dyadicGaussianEnergyConstant γ) * (1 + logCriticalRadial γ r) := by
  by_cases hr₀ : r = 0
  · subst r
    simp only [logCriticalRadial_zero, add_top,
      ENNReal.mul_top (ENNReal.ofReal_pos.mpr (dyadicGaussianEnergyConstant_pos γ)).ne']
    exact le_top
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr₀)
  have hconstant : ENNReal.ofReal (dyadicGaussianBoundConstant γ) ≤
      ENNReal.ofReal (dyadicGaussianEnergyConstant γ) := by
    apply ENNReal.ofReal_le_ofReal
    exact le_add_of_nonneg_right (dyadicGaussianKernel_nonneg γ 1)
  by_cases hr₁ : r < 1
  · have hweight : logWeight r = 1 + Real.log (1 / r) := by
      rw [logWeight, max_eq_right (Real.log_nonneg ((one_le_div₀ hrpos).mpr hr₁.le))]
    have hsmall : ennDyadicGaussianKernel γ r ≤
        ENNReal.ofReal (dyadicGaussianBoundConstant γ) * logCriticalRadial γ r := by
      rw [ennDyadicGaussianKernel_eq_ofReal γ r hγ hrpos, logCriticalRadial, hweight,
        ← mul_assoc, ← ENNReal.ofReal_mul (dyadicGaussianBoundConstant_pos γ).le,
        ← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos hrpos]
      exact ENNReal.ofReal_le_ofReal (dyadicGaussianKernel_le_log γ r hγ hrpos hr₁)
    exact hsmall.trans (mul_le_mul' hconstant (le_add_of_nonneg_left (by positivity)))
  · calc
      ennDyadicGaussianKernel γ r = ENNReal.ofReal (dyadicGaussianKernel γ r) :=
        ennDyadicGaussianKernel_eq_ofReal γ r hγ hrpos
      _ ≤ ENNReal.ofReal (dyadicGaussianKernel γ 1) :=
        ENNReal.ofReal_le_ofReal (dyadicGaussianKernel_le_at_one γ r hγ (le_of_not_gt hr₁))
      _ ≤ ENNReal.ofReal (dyadicGaussianEnergyConstant γ) := by
        apply ENNReal.ofReal_le_ofReal
        exact le_add_of_nonneg_left (dyadicGaussianBoundConstant_pos γ).le
      _ ≤ ENNReal.ofReal (dyadicGaussianEnergyConstant γ) * (1 + logCriticalRadial γ r) := by
        conv_lhs => rw [← mul_one (ENNReal.ofReal (dyadicGaussianEnergyConstant γ))]
        exact mul_le_mul' le_rfl (show (1 : ℝ≥0∞) ≤ 1 + logCriticalRadial γ r from
          le_add_of_nonneg_right (by positivity))

end FalconerThetaGauge
