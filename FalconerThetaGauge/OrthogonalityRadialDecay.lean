module

public import FalconerThetaGauge.OrthogonalityRadialRegularity

/-! # The literal linear-phase radial cancellation in Estimate 7.6 -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace FalconerThetaGauge

theorem norm_integral_orthogonalityRadialAmplitude_le {T K v : ℕ} (hT : 1 ≤ T)
    (hK : 6 * T ≤ K) {τ Φ : ℝ} (hτ : 0 < τ) (hΦ : τ / 2 ≤ |Φ|) :
    ‖∫ r : ℝ, Complex.exp (-((r * Φ : ℝ) : ℂ) * Complex.I) *
        orthogonalityRadialAmplitude K v r‖ ≤
      64 * (4 : ℝ) ^ v * (1024 * (T : ℝ) ^ 2 / ((2 : ℝ) ^ v * τ)) ^ T := by
  let φ : ℝ → ℝ := fun r ↦ -Φ * r
  have hφ : ContDiff ℝ ∞ φ := contDiff_const.mul contDiff_id
  have hder : ∀ r ∈ tsupport (orthogonalityRadialAmplitude K v), deriv φ r = -Φ := by
    intro r hr
    simp only [φ, deriv_const_mul_id]
  have h := linear_phase hφ (contDiff_orthogonalityRadialAmplitude K v)
    (hasCompactSupport_orthogonalityRadialAmplitude K v) (by linarith : 0 < τ / 2)
    (by simpa only [abs_neg] using hΦ) (by positivity : 0 ≤ 16 * (2 : ℝ) ^ v)
    (by positivity : 0 ≤ 512 * (T : ℝ) ^ 2 / (2 : ℝ) ^ v) hder T
    (fun r hr ↦ norm_iteratedDeriv_orthogonalityRadialAmplitude_le_on_support hT hK
      (by omega) hr)
  have heq : (fun r : ℝ ↦ Complex.exp ((φ r : ℂ) * Complex.I) *
      orthogonalityRadialAmplitude K v r) =
      fun r : ℝ ↦ Complex.exp (-((r * Φ : ℝ) : ℂ) * Complex.I) *
        orthogonalityRadialAmplitude K v r := by
    funext r
    congr 2
    simp only [φ, Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  rw [heq] at h
  calc
    _ ≤ volume.real (tsupport (orthogonalityRadialAmplitude K v)) *
        (16 * (2 : ℝ) ^ v) *
          ((512 * (T : ℝ) ^ 2 / (2 : ℝ) ^ v) / (τ / 2)) ^ T := h
    _ ≤ (4 * (2 : ℝ) ^ v) * (16 * (2 : ℝ) ^ v) *
          ((512 * (T : ℝ) ^ 2 / (2 : ℝ) ^ v) / (τ / 2)) ^ T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (volume_tsupport_orthogonalityRadialAmplitude_le K v) (by positivity)) (by positivity)
    _ = _ := by
      have hpow : ((2 : ℝ) ^ v) ^ 2 = (4 : ℝ) ^ v := by
        rw [← pow_mul, Nat.mul_comm v 2, pow_mul]
        norm_num
      rw [show (512 * (T : ℝ) ^ 2 / (2 : ℝ) ^ v) / (τ / 2) =
        1024 * (T : ℝ) ^ 2 / ((2 : ℝ) ^ v * τ) by ring]
      rw [show (4 * (2 : ℝ) ^ v) * (16 * (2 : ℝ) ^ v) =
        64 * ((2 : ℝ) ^ v) ^ 2 by ring, hpow]

end FalconerThetaGauge
