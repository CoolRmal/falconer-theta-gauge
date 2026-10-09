module

public import FalconerThetaGauge.NonstationaryPhaseUniform

/-!
# Sharp decay for a linear phase

When the inverse phase derivative is constant, the transported amplitude is
exactly that constant to the transport order times the actual derivative.
The amplitude scale can therefore be smaller than one.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff

namespace FalconerThetaGauge

theorem nonstationaryAmplitude_const_iterate (c : ℝ) (a : ℝ → ℂ) (k : ℕ) :
    (nonstationaryAmplitude (fun _ ↦ c))^[k] a =
      fun x ↦ (c : ℂ) ^ k * iteratedDeriv k a x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    funext x
    change deriv (fun y ↦ (c : ℂ) * ((c : ℂ) ^ k * iteratedDeriv k a y)) x = _
    have hfun : (fun y ↦ (c : ℂ) * ((c : ℂ) ^ k * iteratedDeriv k a y)) =
        fun y ↦ ((c : ℂ) * (c : ℂ) ^ k) * iteratedDeriv k a y := by funext y; ring
    rw [hfun, deriv_const_mul_field, iteratedDeriv_succ]
    rw [pow_succ]
    ring

/-- The linear-phase part of Lemma 3.4, with the literal derivative scale. -/
theorem linear_phase {φ : ℝ → ℝ} {a : ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    {c lam A M : ℝ} (hlam : 0 < lam) (hc : lam ≤ |c|) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hder : ∀ x ∈ tsupport a, deriv φ x = c) (k : ℕ)
    (hamp : ∀ x ∈ tsupport a, ‖iteratedDeriv k a x‖ ≤ A * M ^ k) :
    ‖∫ x, Complex.exp ((φ x : ℂ) * Complex.I) * a x‖ ≤
      volume.real (tsupport a) * A * (M / lam) ^ k := by
  have hcpos : 0 < |c| := hlam.trans_le hc
  have hcne : c ≠ 0 := abs_pos.mp hcpos
  have hinv : |c|⁻¹ ≤ lam⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hlam hc
  have hqφ : ∀ x ∈ tsupport a, c⁻¹ * deriv φ x = 1 := by
    intro x hx
    rw [hder x hx, inv_mul_cancel₀ hcne]
  have hbound : ∀ x, ‖(nonstationaryAmplitude (fun _ ↦ c⁻¹))^[k] a x‖ ≤
      A * (M / lam) ^ k := by
    intro x
    rw [nonstationaryAmplitude_const_iterate, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_inv]
    by_cases hx : x ∈ tsupport a
    · calc
        _ ≤ |c|⁻¹ ^ k * (A * M ^ k) :=
          mul_le_mul_of_nonneg_left (hamp x hx) (pow_nonneg (by positivity) _)
        _ ≤ lam⁻¹ ^ k * (A * M ^ k) :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (by positivity) hinv k) (mul_nonneg hA (pow_nonneg hM _))
        _ = _ := by simp only [div_eq_mul_inv, mul_pow]; ring
    · rw [image_eq_zero_of_notMem_tsupport
        (fun h ↦ hx (tsupport_iteratedDeriv_subset k a h)), norm_zero, mul_zero]
      positivity
  have hq : ContDiff ℝ ∞ (fun _ : ℝ ↦ c⁻¹) := contDiff_const
  have hsupport := (nonstationaryAmplitude_iterate_properties hq ha hac k).2.2
  have h := norm_integral_oscillatoryPhase_mul_le hφ hq ha hac hqφ
    (by norm_num : (1 : ℝ) ≠ 0) k
  have hL₁ := integral_norm_le_tsupport_mass hac
    (integrable_nonstationaryAmplitude_iterate hq ha hac k) hsupport hbound
  have hsimple : ‖∫ x, oscillatoryPhase φ 1 x * a x‖ ≤
      ∫ x, ‖(nonstationaryAmplitude (fun _ ↦ c⁻¹))^[k] a x‖ := by
    simpa only [abs_one, inv_one, one_pow, one_mul] using h
  have hfinal : ‖∫ x, oscillatoryPhase φ 1 x * a x‖ ≤
      volume.real (tsupport a) * A * (M / lam) ^ k := by
    simpa only [mul_assoc] using hsimple.trans hL₁
  simpa only [oscillatoryPhase, Complex.ofReal_one, one_mul] using hfinal

end FalconerThetaGauge
