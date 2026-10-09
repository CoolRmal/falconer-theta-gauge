module

public import FalconerThetaGauge.SpaceSplittingCaseAFubini

/-! # Actual single signed stationary terms against the second circle integral -/

@[expose] public section

noncomputable section

open MeasureTheory Function
open scoped RealInnerProductSpace

namespace FalconerThetaGauge

theorem norm_integral_spaceSplittingCaseAStationaryTerm_circle_le_source
    {θ : ℝ} {N L v j : ℕ} (hpar : ParameterFacts θ N) (I : Finset ProfileScheduleTest)
    (hcard : I.card ≤ N ^ 2 + 1) (hv : v ≤ N) {h d σ : ℝ} (hh : h ≤ N)
    (hgap : 2 * max (L : ℝ) (tolerance θ N * N) ≤ (v : ℝ) - h)
    (hd : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ d) (hσ : |σ| = 1)
    (hj : j < expansionCount θ N) {c : ℂ}
    (hc : ‖c‖ ≤ (400 * j *
      (max 1 (scheduledSymbolScale (expansionCount θ N) (tolerance θ N * N) I L)) ^ 2) ^ j)
    {b : Plane → UnitCircle → ℝ} (hb : Measurable (uncurry b))
    (hbound : ∀ x w, |b x w| ≤ 1) (y y' : Plane) (hfar : 2 * dist y y' < d) :
    ‖∫ r : ℝ, spaceSplittingCaseAStationaryTerm (8 * expansionCount θ N) v j σ d c r *
      spaceSplittingCircleIntegral b r y y'‖ ≤
        2 * Real.pi * (2 : ℝ) ^ (-400 * (N : ℝ)) := by
  have hd₀ : 0 < d := lt_of_lt_of_le (by positivity) hd
  rw [integral_spaceSplittingCaseAStationaryTerm_circle_eq _ _ _ _ _ _ hd₀ hb hbound y y']
  have hnorm (w : UnitCircle) : ‖(b y w : ℂ) * (b y' w : ℂ) *
      Complex.exp (((σ * Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
      ((Real.sqrt (2 * Real.pi / d) : ℂ) * (d : ℂ)⁻¹ ^ j * c *
        spaceSplittingCaseARadialMoment (8 * expansionCount θ N) v j
          (σ * d + inner ℝ (w : Plane) (y - y')))‖ ≤
        (2 : ℝ) ^ (-400 * (N : ℝ)) := by
    have hm := norm_spaceSplittingCaseA_coefficient_moment_le_source hpar I hcard hv hh
      hgap hd (spaceSplittingCaseA_phase_abs_ge hσ y y' hfar w) hj hc
    have he : ‖Complex.exp (((σ * Real.pi / 4 : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, he, mul_one]
    calc
      _ ≤ 1 * (2 : ℝ) ^ (-400 * (N : ℝ)) := mul_le_mul
        (by simpa only [one_mul] using
          mul_le_mul (hbound y w) (hbound y' w) (abs_nonneg _) (by norm_num)) hm
        (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have hi := norm_integral_le_of_norm_le_const (μ := circleArcLength)
    (Filter.Eventually.of_forall hnorm)
  rw [measureReal_def, circleArcLength_univ,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi)] at hi
  exact hi.trans_eq (mul_comm _ _)

end FalconerThetaGauge
