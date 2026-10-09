module

public import FalconerThetaGauge.QuadraticGaussian

/-!
# Removing damping from the quadratic Fourier pairing

The spatial and dual Gaussian factors have norm at most one when the real
part of the damping is nonnegative. Ordinary dominated convergence therefore
removes the damping against integrable Schwartz tests.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped FourierTransform Topology

namespace FalconerThetaGauge

theorem norm_quadraticGaussian_le_one {b : ℂ} (hb : 0 ≤ b.re) (x : ℝ) :
    ‖quadraticGaussian b x‖ ≤ 1 := by
  rw [quadraticGaussian, Complex.norm_exp, Real.exp_le_one_iff]
  simp only [← Complex.ofReal_pow, Complex.re_mul_ofReal, Complex.neg_re]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) (sq_nonneg x)

theorem norm_quadraticDualGaussian_le_one {b : ℂ} (hb : 0 ≤ b.re) (ξ : ℝ) :
    ‖Complex.exp (-((Real.pi : ℂ) ^ 2 * (ξ : ℂ) ^ 2) / b)‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have hi : 0 ≤ b⁻¹.re := by
    rw [Complex.inv_re]
    exact div_nonneg hb (Complex.normSq_nonneg b)
  have he : (-((Real.pi : ℂ) ^ 2 * (ξ : ℂ) ^ 2) / b).re =
      -(Real.pi ^ 2 * ξ ^ 2) * b⁻¹.re := by
    simp only [div_eq_mul_inv, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      ← Complex.ofReal_neg, Complex.re_ofReal_mul]
  rw [he]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hi

theorem tendsto_integral_quadraticGaussian_mul {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated]
    {b : ι → ℂ} {b₀ : ℂ} (hb : Tendsto b l (𝓝 b₀))
    (hbre : ∀ᶠ i in l, 0 ≤ (b i).re) (g : SchwartzMap ℝ ℂ) :
    Tendsto (fun i ↦ ∫ x, quadraticGaussian (b i) x * g x)
      l (𝓝 (∫ x, quadraticGaussian b₀ x * g x)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x ↦ ‖g x‖) ?_ ?_ g.integrable.norm ?_
  · exact Eventually.of_forall fun i ↦
      ((by unfold quadraticGaussian; fun_prop : Continuous (quadraticGaussian (b i))).mul
        g.continuous).aestronglyMeasurable
  · filter_upwards [hbre] with i hi
    exact Eventually.of_forall fun x ↦ by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (norm_quadraticGaussian_le_one hi x)
        (norm_nonneg _)).trans_eq (one_mul _)
  · exact Eventually.of_forall fun x ↦ by
      exact ((hb.neg.mul_const ((x : ℂ) ^ 2)).cexp).mul_const (g x)

theorem tendsto_integral_quadraticDualGaussian_mul {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated]
    {b : ι → ℂ} {b₀ : ℂ} (hb : Tendsto b l (𝓝 b₀)) (hb₀ : b₀ ≠ 0)
    (hbre : ∀ᶠ i in l, 0 ≤ (b i).re) (g : SchwartzMap ℝ ℂ) :
    Tendsto (fun i ↦ ∫ ξ : ℝ,
      Complex.exp (-((Real.pi : ℂ) ^ 2 * (ξ : ℂ) ^ 2) / b i) * (𝓕⁻ g) ξ)
      l (𝓝 (∫ ξ : ℝ,
        Complex.exp (-((Real.pi : ℂ) ^ 2 * (ξ : ℂ) ^ 2) / b₀) * (𝓕⁻ g) ξ)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun ξ ↦ ‖(𝓕⁻ g) ξ‖) ?_ ?_ (𝓕⁻ g).integrable.norm ?_
  · exact Eventually.of_forall fun i ↦
      ((by fun_prop : Continuous (fun ξ : ℝ ↦
        Complex.exp (-((Real.pi : ℂ) ^ 2 * (ξ : ℂ) ^ 2) / b i))).mul
          (𝓕⁻ g).continuous).aestronglyMeasurable
  · filter_upwards [hbre] with i hi
    exact Eventually.of_forall fun ξ ↦ by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (norm_quadraticDualGaussian_le_one hi ξ)
        (norm_nonneg _)).trans_eq (one_mul _)
  · exact Eventually.of_forall fun ξ ↦
      ((tendsto_const_nhds.div hb hb₀).cexp).mul_const ((𝓕⁻ g) ξ)

end FalconerThetaGauge
