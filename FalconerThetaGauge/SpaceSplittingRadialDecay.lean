module

public import FalconerThetaGauge.SpaceSplittingRadialDerivatives

/-! # Twice-integrated genuine radial moments and the source opposite-sign kernel -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff

namespace FalconerThetaGauge

/-- The actual cutoff-normalized radial moment in the opposite-sign stationary terms. -/
def spaceSplittingRadialMoment (K v : ℕ) (m : ℤ) (δ : ℝ) : ℂ :=
  ∫ r : ℝ, Complex.exp (-((r * δ : ℝ) : ℂ) * Complex.I) *
    spaceSplittingRadialAmplitude K v m r

theorem spaceSplittingRadialMoment_eq_positive_integral (K v : ℕ) (m : ℤ) (δ : ℝ) :
    spaceSplittingRadialMoment K v m δ =
      ((2 : ℝ) ^ v)⁻¹ * ∫ r in Ioi (0 : ℝ),
        (maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) : ℂ) * ((r ^ m : ℝ) : ℂ) *
          Complex.exp (-((r * δ : ℝ) : ℂ) * Complex.I) := by
  unfold spaceSplittingRadialMoment
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) (fun r hr ↦ by
    rw [spaceSplittingRadialAmplitude_eq_zero K v m (fun h ↦ hr
      ((by positivity : (0 : ℝ) < (2 : ℝ) ^ v / 4).trans_le h.1)), mul_zero])]
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  unfold spaceSplittingRadialAmplitude
  push_cast
  ring

theorem norm_spaceSplittingRadialMoment_le_trivial (K v : ℕ) (m : ℤ) (δ : ℝ) :
    ‖spaceSplittingRadialMoment K v m δ‖ ≤ 4 * spaceSplittingRadialBound v m := by
  have hac := hasCompactSupport_spaceSplittingRadialAmplitude K v m
  have ha := contDiff_spaceSplittingRadialAmplitude K v m
  have hi : Integrable (spaceSplittingRadialAmplitude K v m) :=
    ha.continuous.integrable_of_hasCompactSupport hac
  have hnorm := integral_norm_le_tsupport_mass hac hi (subset_refl _)
    (fun r ↦ by
      by_cases hr : r ∈ tsupport (spaceSplittingRadialAmplitude K v m)
      · exact norm_spaceSplittingRadialAmplitude_le_on_support K v m hr
      · rw [image_eq_zero_of_notMem_tsupport hr, norm_zero]
        exact div_nonneg (spaceSplittingRadialBound_pos v m).le (by positivity))
  unfold spaceSplittingRadialMoment
  calc
    _ ≤ ∫ r : ℝ, ‖Complex.exp (-((r * δ : ℝ) : ℂ) * Complex.I) *
        spaceSplittingRadialAmplitude K v m r‖ := norm_integral_le_integral_norm _
    _ = ∫ r : ℝ, ‖spaceSplittingRadialAmplitude K v m r‖ := by
      apply integral_congr_ae
      filter_upwards [] with r
      rw [norm_mul, Complex.norm_exp]
      simp
    _ ≤ volume.real (tsupport (spaceSplittingRadialAmplitude K v m)) *
        (spaceSplittingRadialBound v m / (2 : ℝ) ^ v) := hnorm
    _ ≤ (4 * (2 : ℝ) ^ v) * (spaceSplittingRadialBound v m / (2 : ℝ) ^ v) :=
      mul_le_mul_of_nonneg_right (volume_tsupport_spaceSplittingRadialAmplitude_le K v m)
        (div_nonneg (spaceSplittingRadialBound_pos v m).le (by positivity))
    _ = _ := by field_simp

theorem norm_spaceSplittingRadialMoment_le_second {K v : ℕ} (hK : 2 ≤ K)
    (m : ℤ) {δ : ℝ} (hδ : δ ≠ 0) :
    ‖spaceSplittingRadialMoment K v m δ‖ ≤
      3136 * spaceSplittingRadialBound v m * (|(m : ℝ)| + 1) ^ 2 /
        ((2 : ℝ) ^ v * |δ|) ^ 2 := by
  let φ : ℝ → ℝ := fun r ↦ -δ * r
  have hder : ∀ r ∈ tsupport (spaceSplittingRadialAmplitude K v m), deriv φ r = -δ := by
    intro r _
    simp only [φ, deriv_const_mul_id]
  have h := linear_phase (φ := φ) (contDiff_const.mul contDiff_id)
    (contDiff_spaceSplittingRadialAmplitude K v m)
    (hasCompactSupport_spaceSplittingRadialAmplitude K v m) (abs_pos.mpr hδ)
    (by simp : |δ| ≤ |-δ|)
    (div_nonneg (spaceSplittingRadialBound_pos v m).le
      (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ v))
    (by positivity : 0 ≤ 28 * (|(m : ℝ)| + 1) / (2 : ℝ) ^ v) hder 2
    (fun _ hr ↦ norm_secondDeriv_spaceSplittingRadialAmplitude_le_on_support hK m hr)
  have heq : (fun r : ℝ ↦ Complex.exp ((φ r : ℂ) * Complex.I) *
      spaceSplittingRadialAmplitude K v m r) = fun r : ℝ ↦
        Complex.exp (-((r * δ : ℝ) : ℂ) * Complex.I) *
          spaceSplittingRadialAmplitude K v m r := by
    funext r
    congr 2
    dsimp [φ]
    push_cast
    ring
  rw [heq] at h
  apply h.trans
  calc
    _ ≤ (4 * (2 : ℝ) ^ v) * (spaceSplittingRadialBound v m / (2 : ℝ) ^ v) *
        ((28 * (|(m : ℝ)| + 1) / (2 : ℝ) ^ v) / |δ|) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (volume_tsupport_spaceSplittingRadialAmplitude_le K v m)
        (div_nonneg (spaceSplittingRadialBound_pos v m).le (by positivity)))
        (sq_nonneg _)
    _ = _ := by field_simp; ring

/-- The exact elementary conversion from two integrations by parts to the source decay kernel. -/
theorem scalar_second_decay_le_kernel {z A B x : ℝ} (hz : 0 ≤ z) (hA : 0 ≤ A)
    (hB : 1 ≤ B) (hx : 0 ≤ x) (htrivial : z ≤ A)
    (hsecond : x ≠ 0 → z ≤ A * B / x ^ 2) : z ≤ 4 * A * B / (1 + x) ^ 2 := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (1 + x) ^ 2)).2
  by_cases hxone : x ≤ 1
  · have hsq : (1 + x) ^ 2 ≤ 4 := by nlinarith
    calc
      _ ≤ z * 4 := mul_le_mul_of_nonneg_left hsq hz
      _ ≤ A * 4 := mul_le_mul_of_nonneg_right htrivial (by norm_num)
      _ ≤ _ := by nlinarith
  · have hxpos : 0 < x := lt_of_le_of_lt (by norm_num : (0 : ℝ) ≤ 1) (lt_of_not_ge hxone)
    have hmul := (le_div_iff₀ (sq_pos_of_pos hxpos)).1 (hsecond hxpos.ne')
    have hsq : (1 + x) ^ 2 ≤ 4 * x ^ 2 := by nlinarith
    calc
      _ ≤ z * (4 * x ^ 2) := mul_le_mul_of_nonneg_left hsq hz
      _ = 4 * (z * x ^ 2) := by ring
      _ ≤ 4 * (A * B) := mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = _ := by ring

/-- The true opposite-sign radial integral has the manuscript's explicit `12544` kernel bound. -/
theorem norm_spaceSplittingRadialMoment_le_kernel {K v : ℕ} (hK : 2 ≤ K)
    (m : ℤ) (δ : ℝ) :
    ‖spaceSplittingRadialMoment K v m δ‖ ≤
      12544 * spaceSplittingRadialBound v m * (|(m : ℝ)| + 1) ^ 2 /
        (1 + (2 : ℝ) ^ v * |δ|) ^ 2 := by
  have hB : 1 ≤ 784 * (|(m : ℝ)| + 1) ^ 2 := by nlinarith [abs_nonneg (m : ℝ)]
  have h := scalar_second_decay_le_kernel
    (norm_nonneg (spaceSplittingRadialMoment K v m δ))
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (spaceSplittingRadialBound_pos v m).le)
    hB (by positivity : 0 ≤ (2 : ℝ) ^ v * |δ|)
    (norm_spaceSplittingRadialMoment_le_trivial K v m δ) (fun hne ↦ by
      have hδ : δ ≠ 0 := by intro hδ; simp [hδ] at hne
      convert norm_spaceSplittingRadialMoment_le_second hK m hδ using 1
      ring)
  convert h using 1
  ring

end FalconerThetaGauge
