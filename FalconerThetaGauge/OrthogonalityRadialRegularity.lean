module

public import FalconerThetaGauge.OrthogonalityRadialDerivatives

/-! # The exact source radial derivative scale `512 T² 2⁻ᵛ` -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace FalconerThetaGauge

theorem norm_iteratedDeriv_orthogonalityRadialAmplitude_le_on_support {T K v j : ℕ}
    (hT : 1 ≤ T) (hK : 6 * T ≤ K) (hj : j ≤ 6 * T) {r : ℝ}
    (hr : r ∈ tsupport (orthogonalityRadialAmplitude K v)) :
    ‖iteratedDeriv j (orthogonalityRadialAmplitude K v) r‖ ≤
      (16 * (2 : ℝ) ^ v) * (512 * (T : ℝ) ^ 2 / (2 : ℝ) ^ v) ^ j := by
  let s : ℝ := (2 : ℝ) ^ v
  have hs : 0 < s := by dsimp [s]; positivity
  have hr' : r ∈ Icc 0 (4 * s) := by
    have h := tsupport_orthogonalityRadialAmplitude_subset K v hr
    exact ⟨le_trans (by positivity) h.1, h.2⟩
  let f : ℝ → ℂ := fun x ↦ (maskedFrequencyCutoff K (x / s) : ℂ)
  let g : ℝ → ℂ := fun x ↦ (x : ℂ) ^ 2
  have hf : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp
    ((contDiff_maskedFrequencyCutoff K).comp (contDiff_id.div_const s))
  have hg : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.pow 2
  have hprod := norm_iteratedDeriv_mul_le_at (A := 1) (B := 16 * s ^ 2)
    hf hg (by norm_num) (by positivity)
    (by positivity : 0 ≤ 504 * (T : ℝ) ^ 2 / s) (by positivity : 0 ≤ s⁻¹) j r
    (fun i hi ↦ by simpa only [one_mul] using
      norm_iteratedDeriv_scaled_frequencyCutoff_le hK (hi.trans hj) hs r)
    (fun i _ ↦ norm_iteratedDeriv_complex_square_le hs hr' i)
  have heq : orthogonalityRadialAmplitude K v = fun x ↦ (s⁻¹ : ℂ) * (f * g) x := by
    funext x
    dsimp only [orthogonalityRadialAmplitude, s, f, g, Pi.mul_apply]
    simp only [Complex.ofReal_pow, Complex.ofReal_ofNat]
    ring
  rw [heq, iteratedDeriv_const_mul_field, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hs]
  calc
    _ ≤ s⁻¹ * ((1 * (16 * s ^ 2)) * (504 * (T : ℝ) ^ 2 / s + s⁻¹) ^ j) :=
      mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr hs.le)
    _ ≤ s⁻¹ * ((16 * s ^ 2) * (512 * (T : ℝ) ^ 2 / s) ^ j) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hs.le)
      simp only [one_mul]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
      rw [← one_div, ← add_div]
      exact div_le_div_of_nonneg_right (by nlinarith) hs.le
    _ = _ := by
      change _ = (16 * s) * _
      dsimp only [s]
      field_simp

end FalconerThetaGauge
