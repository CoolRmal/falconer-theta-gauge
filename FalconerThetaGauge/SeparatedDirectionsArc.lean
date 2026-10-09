module

public import FalconerThetaGauge.GaugeSeparatedMeasuresGeometry
public import FalconerThetaGauge.ExplicitBumpCircle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # The common short arc forced by the prepared support discs -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerThetaGauge

/-- A closed oriented circular arc, parameterized by a literal real angular interval. -/
def closedDirectionArc (α r : ℝ) : Set UnitCircle :=
  unitCircleOfAngle '' Icc (α - r) (α + r)

theorem isCompact_closedDirectionArc (α r : ℝ) : IsCompact (closedDirectionArc α r) :=
  isCompact_Icc.image continuous_unitCircleOfAngle

/-- A complex displacement within two percent of `1` turns by less than `1/40`. -/
theorem abs_arg_lt_one_fortieth_of_norm_sub_one_lt {z : ℂ}
    (hz : ‖z - 1‖ < 1 / 50) : |z.arg| < 1 / 40 := by
  have hre : |z.re - 1| < 1 / 50 := by
    simpa only [Complex.sub_re, Complex.one_re] using
      (Complex.abs_re_le_norm (z - 1)).trans_lt hz
  have him : |z.im| < 1 / 50 := by
    simpa only [Complex.sub_im, Complex.one_im, sub_zero] using
      (Complex.abs_im_le_norm (z - 1)).trans_lt hz
  have hre' : 0 < z.re := by have := (abs_lt.mp hre).1; linarith
  have hangle := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre'))
  have harg : z.arg = Real.arctan (z.im / z.re) := by
    rw [← Complex.tan_arg z]
    exact (Real.arctan_tan hangle.1 hangle.2).symm
  rw [harg]
  apply Real.abs_arctan_le_abs.trans_lt
  rw [abs_div, abs_of_pos hre']
  apply (div_lt_iff₀ hre').mpr
  have := (abs_lt.mp hre).1
  linarith

/-- Polar normalization respects multiplication, so the relative angle can be kept on
one real branch even when the absolute center angle crosses the usual branch cut. -/
theorem complex_normalized_mul_angle {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) :
    (Real.cos (u.arg + v.arg) + Real.sin (u.arg + v.arg) * Complex.I : ℂ) =
      ((‖u * v‖ : ℝ) : ℂ)⁻¹ * (u * v) := by
  have hnorm : (‖u * v‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr (mul_ne_zero hu hv)
  apply (eq_inv_mul_iff_mul_eq₀ hnorm).mpr
  rw [Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I,
    Complex.ofReal_add, add_mul, Complex.exp_add, norm_mul, Complex.ofReal_mul]
  calc
    ((‖u‖ : ℂ) * (‖v‖ : ℂ)) *
        (Complex.exp (u.arg * Complex.I) * Complex.exp (v.arg * Complex.I)) =
      ((‖u‖ : ℂ) * Complex.exp (u.arg * Complex.I)) *
        ((‖v‖ : ℂ) * Complex.exp (v.arg * Complex.I)) := by ring
    _ = u * v := by rw [Complex.norm_mul_exp_arg_mul_I, Complex.norm_mul_exp_arg_mul_I]

/-- The manuscript's oriented pair directions for the two actual preparation discs
belong to the same closed arc of angular length `1/20`. -/
theorem prepared_pairDirection_mem_closedDirectionArc {a b x y : Plane}
    (hab : dist a b = 1 / 4) (hx : x ∈ Metric.ball a (1 / 400))
    (hy : y ∈ Metric.ball b (1 / 400)) :
    pairDirection x y ∈ closedDirectionArc (radialAngle b a) (1 / 40) := by
  let u : ℂ := Complex.orthonormalBasisOneI.repr.symm (a - b)
  let v : ℂ := Complex.orthonormalBasisOneI.repr.symm (x - y)
  have hu_norm : ‖u‖ = 1 / 4 := by
    simpa only [u, LinearIsometryEquiv.norm_map, ← dist_eq_norm] using hab
  have hu : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu_norm]; norm_num)
  have hxy : x ≠ y := by
    have hdist := (GaugeSeparatedMeasures.prepared_balls_distance_bounds hab hx hy).1
    apply dist_pos.mp
    linarith
  have hdiff : ‖v - u‖ < 1 / 200 := by
    have heq : (x - y) - (a - b) = (x - a) - (y - b) := by abel
    have hle := norm_sub_le (x - a) (y - b)
    have hxa := Metric.mem_ball.mp hx
    have hyb := Metric.mem_ball.mp hy
    change ‖Complex.orthonormalBasisOneI.repr.symm (x - y) -
      Complex.orthonormalBasisOneI.repr.symm (a - b)‖ < 1 / 200
    rw [← map_sub, LinearIsometryEquiv.norm_map, heq]
    rw [dist_eq_norm] at hxa hyb
    linarith
  let q : ℂ := v / u
  have hq_close : ‖q - 1‖ < 1 / 50 := by
    change ‖v / u - 1‖ < 1 / 50
    rw [div_sub_one hu, norm_div, hu_norm]
    exact (div_lt_iff₀ (by norm_num : (0 : ℝ) < 1 / 4)).mpr (by linarith)
  have hq : q ≠ 0 := by
    intro hzero
    simp only [hzero, zero_sub, norm_neg, norm_one] at hq_close
    norm_num at hq_close
  have hq_angle := abs_arg_lt_one_fortieth_of_norm_sub_one_lt hq_close
  have huv : u * q = v := by
    dsimp [q]
    exact mul_div_cancel₀ v hu
  have hdir : angularDirection (radialAngle b a + q.arg) = (pairDirection x y : Plane) := by
    rw [coe_pairDirection_of_ne hxy]
    change Complex.orthonormalBasisOneI.repr
        ((Real.cos (u.arg + q.arg) + Real.sin (u.arg + q.arg) * Complex.I : ℂ)) =
      ‖x - y‖⁻¹ • (x - y)
    rw [complex_normalized_mul_angle hu hq, huv]
    simp only [v, LinearIsometryEquiv.norm_map, ← Complex.ofReal_inv,
      ← Complex.real_smul, map_smul, LinearIsometryEquiv.apply_symm_apply]
  refine ⟨radialAngle b a + q.arg, ?_, ?_⟩
  · have h := abs_lt.mp hq_angle
    constructor <;> linarith
  · exact Subtype.ext hdir

/-- The same center angle and common arc work simultaneously for every pair of
points in the two actual prepared carriers, with a consistent orientation. -/
theorem prepared_carriers_common_direction_arc {a b : Plane} (hab : dist a b = 1 / 4)
    {S₁ S₂ : Set Plane} (hS₁ : S₁ ⊆ Metric.ball a (1 / 400))
    (hS₂ : S₂ ⊆ Metric.ball b (1 / 400)) :
    ∃ α : ℝ, ∀ x ∈ S₁, ∀ y ∈ S₂,
      pairDirection x y ∈ closedDirectionArc α (1 / 40) :=
  ⟨radialAngle b a, fun _ hx _ hy ↦
    prepared_pairDirection_mem_closedDirectionArc hab (hS₁ hx) (hS₂ hy)⟩

end FalconerThetaGauge
