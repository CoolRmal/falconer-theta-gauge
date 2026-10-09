module

public import FalconerThetaGauge.QuadraticGaussianLimit

/-!
# Genuine undamped quadratic Fourier duality

The identity is obtained as a limit of absolutely integrable Gaussian
pairings. No Fourier transform of a nonintegrable phase is postulated.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped FourierTransform Topology

namespace FalconerThetaGauge

/-- Removing positive real damping from the actual quadratic pairing. -/
theorem integral_quadraticGaussian_mul_schwartz_of_re_zero
    {b₀ : ℂ} (hre : b₀.re = 0) (him : b₀.im ≠ 0) (g : SchwartzMap ℝ ℂ) :
    (∫ x, quadraticGaussian b₀ x * g x) =
      ((Real.pi : ℂ) / b₀) ^ (1 / 2 : ℂ) *
        ∫ ξ : ℝ, Complex.exp (-((Real.pi : ℂ) ^ 2 * (ξ : ℂ) ^ 2) / b₀) * (𝓕⁻ g) ξ := by
  have hb₀ : b₀ ≠ 0 := fun h ↦ him (by rw [h]; rfl)
  let b : ℝ → ℂ := fun c ↦ (c⁻¹ : ℝ) + b₀
  have hb : Tendsto b atTop (𝓝 b₀) := by
    simpa only [Complex.ofReal_zero, zero_add] using
      tendsto_inv_atTop_zero.ofReal.add_const b₀
  have hbr : ∀ᶠ c in atTop, 0 < (b c).re := by
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
    simpa only [b, Complex.add_re, Complex.ofReal_re, hre, add_zero] using inv_pos.mpr hc
  have hbs : (Real.pi : ℂ) / b₀ ∈ Complex.slitPlane := by
    apply Or.inr
    simp only [Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      zero_div, zero_sub]
    exact neg_ne_zero.mpr (div_ne_zero (mul_ne_zero Real.pi_ne_zero him)
      (by simpa only [ne_eq, Complex.normSq_eq_zero] using hb₀))
  have hcoef : Tendsto (fun c ↦ ((Real.pi : ℂ) / b c) ^ (1 / 2 : ℂ)) atTop
      (𝓝 (((Real.pi : ℂ) / b₀) ^ (1 / 2 : ℂ))) :=
    (tendsto_const_nhds.div hb hb₀).cpow tendsto_const_nhds hbs
  have hleft := tendsto_integral_quadraticGaussian_mul hb (hbr.mono fun _ h ↦ h.le) g
  have hright := hcoef.mul
    (tendsto_integral_quadraticDualGaussian_mul hb hb₀ (hbr.mono fun _ h ↦ h.le) g)
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards [hbr] with c hc
  exact (integral_quadraticGaussian_mul_schwartz hc g).symm

end FalconerThetaGauge
