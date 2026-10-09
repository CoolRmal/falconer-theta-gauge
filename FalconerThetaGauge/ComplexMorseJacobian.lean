module

public import FalconerThetaGauge.StationaryMorseAngle
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# A genuine holomorphic Jacobian for the circular Morse coordinate

The inverse square root is taken on the principal complex branch. The
small complex discs stay in the positive half-plane before taking the power.
-/

@[expose] public section

noncomputable section

open Set Metric Filter
open scoped Topology

namespace FalconerThetaGauge

def complexMorseJacobian (z : ℂ) : ℂ := (1 - z ^ 2 / 4) ^ (-1 / 2 : ℂ)

theorem complexMorseBase_bounds {z : ℂ} (hz : ‖z‖ ≤ 3 / 2) :
    0 < (1 - z ^ 2 / 4).re ∧ (7 / 16 : ℝ) ≤ ‖1 - z ^ 2 / 4‖ := by
  have hsmall : ‖z ^ 2 / (4 : ℂ)‖ ≤ (9 / 16 : ℝ) := by
    rw [norm_div, norm_pow]
    norm_num
    nlinarith [norm_nonneg z]
  constructor
  · rw [Complex.sub_re, Complex.one_re]
    linarith [Complex.re_le_norm (z ^ 2 / 4)]
  · have h := norm_sub_norm_le (1 : ℂ) (z ^ 2 / 4)
    rw [norm_one] at h
    linarith

theorem norm_complexMorseJacobian_le_two {z : ℂ} (hz : ‖z‖ ≤ 3 / 2) :
    ‖complexMorseJacobian z‖ ≤ 2 := by
  have hb := (complexMorseBase_bounds hz).2
  have hs : (1 / 2 : ℝ) ≤ Real.sqrt ‖1 - z ^ 2 / 4‖ :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have he : (-1 / 2 : ℂ) = ((-(1 / 2 : ℝ)) : ℂ) := by norm_num
  rw [complexMorseJacobian, he, ← Complex.ofReal_neg, Complex.norm_cpow_real,
    Real.rpow_neg (norm_nonneg _), ← Real.sqrt_eq_rpow]
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hs
  simpa only [one_div, inv_div, inv_one, mul_one, inv_inv] using h

theorem differentiableAt_complexMorseJacobian {z : ℂ} (hz : ‖z‖ ≤ 3 / 2) :
    DifferentiableAt ℂ complexMorseJacobian z := by
  apply DifferentiableAt.cpow_const (by fun_prop)
  exact Complex.mem_slitPlane_iff.mpr (Or.inl (complexMorseBase_bounds hz).1)

theorem norm_complex_near_real_le {s : ℝ} (hs : |s| ≤ 1) {z : ℂ}
    (hz : z ∈ closedBall (s : ℂ) (1 / 2)) : ‖z‖ ≤ 3 / 2 := by
  have hdist : ‖z - (s : ℂ)‖ ≤ (1 / 2 : ℝ) := by
    simpa only [mem_closedBall, dist_eq_norm] using hz
  have hnorm : ‖(s : ℂ)‖ ≤ 1 := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hs
  have h := norm_add_le (z - (s : ℂ)) (s : ℂ)
  rw [sub_add_cancel] at h
  linarith

theorem diffContOnCl_complexMorseJacobian {s : ℝ} (hs : |s| ≤ 1) :
    DiffContOnCl ℂ complexMorseJacobian (ball (s : ℂ) (1 / 2)) := by
  apply DifferentiableOn.diffContOnCl
  rw [closure_ball (s : ℂ) (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  intro z hz
  exact (differentiableAt_complexMorseJacobian
    (norm_complex_near_real_le hs hz)).differentiableWithinAt

/-- Actual Cauchy estimates, uniform over the whole real localization interval. -/
theorem norm_iteratedDeriv_complexMorseJacobian_le (n : ℕ) {s : ℝ} (hs : |s| ≤ 1) :
    ‖iteratedDeriv n complexMorseJacobian (s : ℂ)‖ ≤ 2 * (n.factorial : ℝ) * 2 ^ n := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0 : ℝ) < 1 / 2) (diffContOnCl_complexMorseJacobian hs)
    (fun z hz ↦ norm_complexMorseJacobian_le_two
      (norm_complex_near_real_le hs (sphere_subset_closedBall hz)))
  convert h using 1
  simp only [div_pow, one_pow, div_div_eq_mul_div, div_one]
  ring

/-- Restricting a holomorphic function to the real axis commutes with every derivative. -/
theorem iteratedDeriv_real_of_complex {f : ℂ → ℂ} {s : ℝ}
    (hf : AnalyticAt ℂ f (s : ℂ)) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ ↦ (f x).re) s = (iteratedDeriv n f (s : ℂ)).re := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    have ha : ∀ᶠ x : ℝ in 𝓝 s, AnalyticAt ℂ f (x : ℂ) :=
      (Complex.continuous_ofReal.tendsto s).eventually hf.eventually_analyticAt
    have he : deriv (fun x : ℝ ↦ (f x).re) =ᶠ[𝓝 s]
        (fun x : ℝ ↦ (deriv f x).re) := by
      filter_upwards [ha] with x hx
      exact hx.differentiableAt.hasDerivAt.real_of_complex.deriv
    rw [he.iteratedDeriv_eq n]
    exact ih hf.deriv

theorem analyticAt_complexMorseJacobian {z : ℂ} (hz : ‖z‖ < 3 / 2) :
    AnalyticAt ℂ complexMorseJacobian z := by
  apply DifferentiableOn.analyticAt (s := ball (0 : ℂ) (3 / 2))
  · intro w hw
    have hw' : ‖w‖ < 3 / 2 := by
      simpa only [mem_ball, dist_zero_right] using hw
    exact (differentiableAt_complexMorseJacobian hw'.le).differentiableWithinAt
  · exact isOpen_ball.mem_nhds (by simpa only [mem_ball, dist_zero_right] using hz)

theorem complexMorseJacobian_ofReal {s : ℝ} (hs : |s| ≤ 3 / 2) :
    complexMorseJacobian (s : ℂ) = (stationaryMorseJacobian s : ℂ) := by
  have hb : 0 < 1 - s ^ 2 / 4 := by
    rcases abs_le.mp hs with ⟨hlo, hhi⟩
    nlinarith [sq_nonneg (s + 3 / 2), sq_nonneg (s - 3 / 2)]
  have he : (-1 / 2 : ℂ) = ((-(1 / 2 : ℝ)) : ℂ) := by norm_num
  rw [complexMorseJacobian, show (1 - (s : ℂ) ^ 2 / 4) =
    ((1 - s ^ 2 / 4 : ℝ) : ℂ) by push_cast; rfl, he]
  rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow hb.le,
    Real.rpow_neg hb.le, ← Real.sqrt_eq_rpow]
  simp only [stationaryMorseJacobian, Complex.ofReal_inv]

/-- The real Jacobian obeys actual uniform factorial derivative bounds. -/
theorem norm_iteratedDeriv_stationaryMorseJacobian_le (n : ℕ) {s : ℝ} (hs : |s| ≤ 1) :
    ‖iteratedDeriv n stationaryMorseJacobian s‖ ≤ 2 * (n.factorial : ℝ) * 2 ^ n := by
  have hnorm : ‖(s : ℂ)‖ < 3 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith
  have he : stationaryMorseJacobian =ᶠ[𝓝 s]
      (fun x : ℝ ↦ (complexMorseJacobian x).re) := by
    have hcont : Continuous fun x : ℝ ↦ |x| := continuous_abs
    have hh : ∀ᶠ x : ℝ in 𝓝 s, |x| < 3 / 2 :=
      (hcont.tendsto s).eventually (eventually_lt_nhds (by linarith : |s| < 3 / 2))
    filter_upwards [hh] with x hx
    rw [complexMorseJacobian_ofReal hx.le, Complex.ofReal_re]
  rw [he.iteratedDeriv_eq n,
    iteratedDeriv_real_of_complex (analyticAt_complexMorseJacobian hnorm)]
  exact (RCLike.norm_re_le_norm _).trans (norm_iteratedDeriv_complexMorseJacobian_le n hs)

theorem norm_iteratedDeriv_stationaryMorseAngle_succ_le (n : ℕ) {s : ℝ}
    (hs : |s| ≤ 1) :
    ‖iteratedDeriv (n + 1) stationaryMorseAngle s‖ ≤ 2 * (n.factorial : ℝ) * 2 ^ n := by
  have hi : s ∈ Ioo (-2 : ℝ) 2 := by
    rcases abs_le.mp hs with ⟨hlo, hhi⟩
    constructor <;> linarith
  have he : deriv stationaryMorseAngle =ᶠ[𝓝 s] stationaryMorseJacobian := by
    filter_upwards [isOpen_Ioo.mem_nhds hi] with x hx
    exact deriv_stationaryMorseAngle hx
  rw [iteratedDeriv_succ', he.iteratedDeriv_eq n]
  exact norm_iteratedDeriv_stationaryMorseJacobian_le n hs

end FalconerThetaGauge
