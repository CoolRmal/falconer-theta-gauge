module

public import FalconerThetaGauge.SpaceSplittingRadialRegularity
public import FalconerThetaGauge.SpaceSplittingRadialOrders

/-! # Genuine arbitrary-order linear cancellation for the equal stationary signs -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace FalconerThetaGauge

theorem norm_spaceSplittingRadialMoment_le_linear {T K v : ℕ}
    (hT : 1 ≤ T) (hK : 6 * T ≤ K) {m : ℤ} (hm : |(m : ℝ)| ≤ 2 * T)
    {δ : ℝ} (hδ : δ ≠ 0) :
    ‖spaceSplittingRadialMoment K v m δ‖ ≤
      4 * spaceSplittingRadialBound v m *
        (600 * (T : ℝ) ^ 2 / ((2 : ℝ) ^ v * |δ|)) ^ T := by
  let φ : ℝ → ℝ := fun r ↦ -δ * r
  have hder : ∀ r ∈ tsupport (spaceSplittingRadialAmplitude K v m), deriv φ r = -δ := by
    intro r _
    simp only [φ, deriv_const_mul_id]
  have h := linear_phase (φ := φ) (contDiff_const.mul contDiff_id)
    (contDiff_spaceSplittingRadialAmplitude K v m)
    (hasCompactSupport_spaceSplittingRadialAmplitude K v m) (abs_pos.mpr hδ)
    (by simp : |δ| ≤ |-δ|)
    (div_nonneg (spaceSplittingRadialBound_pos v m).le (by positivity))
    (by positivity : 0 ≤ 600 * (T : ℝ) ^ 2 / (2 : ℝ) ^ v) hder T
    (fun _ hr ↦ norm_iteratedDeriv_spaceSplittingRadialAmplitude_le hT hK
      (by omega) hm hr)
  have heq : (fun r : ℝ ↦ Complex.exp ((φ r : ℂ) * Complex.I) *
      spaceSplittingRadialAmplitude K v m r) = fun r : ℝ ↦
        Complex.exp (-((r * δ : ℝ) : ℂ) * Complex.I) *
          spaceSplittingRadialAmplitude K v m r := by
    funext r
    congr 2
    simp only [φ, Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  rw [heq] at h
  calc
    _ ≤ volume.real (tsupport (spaceSplittingRadialAmplitude K v m)) *
        (spaceSplittingRadialBound v m / (2 : ℝ) ^ v) *
          ((600 * (T : ℝ) ^ 2 / (2 : ℝ) ^ v) / |δ|) ^ T := h
    _ ≤ (4 * (2 : ℝ) ^ v) * (spaceSplittingRadialBound v m / (2 : ℝ) ^ v) *
          ((600 * (T : ℝ) ^ 2 / (2 : ℝ) ^ v) / |δ|) ^ T :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (volume_tsupport_spaceSplittingRadialAmplitude_le K v m)
          (div_nonneg (spaceSplittingRadialBound_pos v m).le (by positivity))) (by positivity)
    _ = _ := by
      rw [show (600 * (T : ℝ) ^ 2 / (2 : ℝ) ^ v) / |δ| =
        600 * (T : ℝ) ^ 2 / ((2 : ℝ) ^ v * |δ|) by ring]
      field_simp

theorem stationary_orders_abs_le_two_order {T j k : ℕ} (hT : 1 ≤ T)
    (hj : j < T) (hk : k < T) : |((1 - (j : ℤ) - k : ℤ) : ℝ)| ≤ 2 * T := by
  have h := stationary_orders_abs_le j k
  have hj' : (j : ℝ) + 1 ≤ T := by exact_mod_cast hj
  have hk' : (k : ℝ) + 1 ≤ T := by exact_mod_cast hk
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  linarith

/-- Equal signs have the actual sum-distance phase, so repeated cancellation applies. -/
theorem norm_spaceSplittingEqualSignMoment_le {T K v j k : ℕ}
    (hT : 1 ≤ T) (hK : 6 * T ≤ K) (hj : j < T) (hk : k < T)
    {dx dy : ℝ} (hdx : 0 < dx) (hdy : 0 < dy) :
    ‖spaceSplittingRadialMoment K v (1 - (j : ℤ) - k) (dx + dy)‖ ≤
      4 * spaceSplittingRadialBound v (1 - (j : ℤ) - k) *
        (600 * (T : ℝ) ^ 2 / ((2 : ℝ) ^ v * (dx + dy))) ^ T := by
  simpa only [abs_of_pos (add_pos hdx hdy)] using
    norm_spaceSplittingRadialMoment_le_linear hT hK
      (stationary_orders_abs_le_two_order hT hj hk) (add_pos hdx hdy).ne'

end FalconerThetaGauge
