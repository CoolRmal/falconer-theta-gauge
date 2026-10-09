module

public import FalconerThetaGauge.SpaceSplittingRealPowerDerivatives
public import FalconerThetaGauge.LinearPhase
public import FalconerThetaGauge.RadialProjectionDefinitions

/-! # Genuine radial cancellation in the separated-scale Case A phase -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff RealInnerProductSpace

namespace FalconerThetaGauge

def spaceSplittingCaseARadialMoment (K v j : ℕ) (Φ : ℝ) : ℂ :=
  ∫ r : ℝ, Complex.exp (-((r * Φ : ℝ) : ℂ) * Complex.I) *
    spaceSplittingCaseAAmplitude K v j r

theorem norm_spaceSplittingCaseARadialMoment_le_linear {T K v j : ℕ}
    (hT : 1 ≤ T) (hK : 6 * T ≤ K) (hj : j < T)
    {d Φ : ℝ} (hd : 0 < d) (hΦ : d / 2 ≤ |Φ|) :
    ‖spaceSplittingCaseARadialMoment K v j Φ‖ ≤
      4 * (2 : ℝ) ^ v * spaceSplittingCaseABound v j *
        (1200 * (T : ℝ) ^ 2 / ((2 : ℝ) ^ v * d)) ^ T := by
  let φ : ℝ → ℝ := fun r ↦ -Φ * r
  have hder : ∀ r ∈ tsupport (spaceSplittingCaseAAmplitude K v j), deriv φ r = -Φ := by
    intro r _
    simp only [φ, deriv_const_mul_id]
  have h := linear_phase (φ := φ) (a := spaceSplittingCaseAAmplitude K v j)
    (contDiff_const.mul contDiff_id)
    (contDiff_spaceSplittingRealPowerAmplitude K v _)
    (hasCompactSupport_spaceSplittingRealPowerAmplitude K v _) (by positivity : 0 < d / 2)
    (by simpa only [abs_neg] using hΦ) (by
      unfold spaceSplittingCaseABound
      positivity) (by positivity : 0 ≤ 600 * (T : ℝ) ^ 2 / (2 : ℝ) ^ v) hder T
    (fun r hr ↦ norm_iteratedDeriv_spaceSplittingCaseAAmplitude_le hT hK hj (by omega) hr)
  have heq : (fun r : ℝ ↦ Complex.exp ((φ r : ℂ) * Complex.I) *
      spaceSplittingCaseAAmplitude K v j r) = fun r : ℝ ↦
        Complex.exp (-((r * Φ : ℝ) : ℂ) * Complex.I) *
          spaceSplittingCaseAAmplitude K v j r := by
    funext r
    congr 2
    simp only [φ, Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  rw [heq] at h
  calc
    _ ≤ volume.real (tsupport (spaceSplittingCaseAAmplitude K v j)) *
        spaceSplittingCaseABound v j *
        ((600 * (T : ℝ) ^ 2 / (2 : ℝ) ^ v) / (d / 2)) ^ T := h
    _ ≤ (4 * (2 : ℝ) ^ v) * spaceSplittingCaseABound v j *
        ((600 * (T : ℝ) ^ 2 / (2 : ℝ) ^ v) / (d / 2)) ^ T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (volume_tsupport_spaceSplittingRealPowerAmplitude_le K v _)
        (by unfold spaceSplittingCaseABound; positivity)) (by positivity)
    _ = _ := by
      rw [show (600 * (T : ℝ) ^ 2 / (2 : ℝ) ^ v) / (d / 2) =
        1200 * (T : ℝ) ^ 2 / ((2 : ℝ) ^ v * d) by ring]

/-- The actual second angular direction cannot cancel the larger spatial distance in Case A. -/
theorem spaceSplittingCaseA_phase_abs_ge {d σ : ℝ} (hσ : |σ| = 1)
    (y y' : Plane) (hd : 2 * dist y y' < d) (w : UnitCircle) :
    d / 2 ≤ |σ * d + inner ℝ (w : Plane) (y - y')| := by
  have hd₀ : 0 < d := lt_of_le_of_lt (by positivity) hd
  have hi := abs_real_inner_le_norm (w : Plane) (y - y')
  have hw : ‖(w : Plane)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using w.property
  rw [hw, one_mul, ← dist_eq_norm] at hi
  have hh := abs_add_le (σ * d + inner ℝ (w : Plane) (y - y'))
    (-inner ℝ (w : Plane) (y - y'))
  simp only [add_neg_cancel_right, abs_neg, abs_mul, hσ, one_mul, abs_of_pos hd₀] at hh
  linarith

theorem norm_spaceSplittingCaseARadialMoment_le_spatial {T K v j : ℕ}
    (hT : 1 ≤ T) (hK : 6 * T ≤ K) (hj : j < T) {d σ : ℝ} (hσ : |σ| = 1)
    (y y' : Plane) (hd : 2 * dist y y' < d) (w : UnitCircle) :
    ‖spaceSplittingCaseARadialMoment K v j
      (σ * d + inner ℝ (w : Plane) (y - y'))‖ ≤
      4 * (2 : ℝ) ^ v * spaceSplittingCaseABound v j *
        (1200 * (T : ℝ) ^ 2 / ((2 : ℝ) ^ v * d)) ^ T := by
  apply norm_spaceSplittingCaseARadialMoment_le_linear hT hK hj
    (lt_of_le_of_lt (by positivity) hd)
  exact spaceSplittingCaseA_phase_abs_ge hσ y y' hd w

end FalconerThetaGauge
