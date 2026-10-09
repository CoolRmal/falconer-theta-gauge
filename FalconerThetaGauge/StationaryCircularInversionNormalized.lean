module

public import FalconerThetaGauge.StationaryCircularInversionGeometric

/-! # The literal normalized pointwise circular inversion in source (7.4) -/

@[expose] public section

noncomputable section

open Finset Function
open scoped ContDiff

namespace FalconerThetaGauge

def preparedCircleInversionConstant : ℂ :=
  (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
    Complex.exp (-((Real.pi / 4 : ℝ) : ℂ) * Complex.I)

theorem norm_preparedCircleInversionConstant :
    ‖preparedCircleInversionConstant‖ = (Real.sqrt (2 * Real.pi))⁻¹ := by
  simp [preparedCircleInversionConstant, Complex.norm_exp, Complex.mul_re,
    Complex.norm_real, abs_of_nonneg (Real.sqrt_nonneg _)]

theorem normalized_circular_square_root {r d : ℝ} (hr : 0 < r) (hd : 0 < d) :
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt r *
      Real.sqrt (2 * Real.pi / (r * d)) = (Real.sqrt d)⁻¹ := by
  rw [Real.sqrt_div (by positivity) _, Real.sqrt_mul hr.le]
  have hp : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have hr' : Real.sqrt r ≠ 0 := by positivity
  have hd' : Real.sqrt d ≠ 0 := by positivity
  field_simp

theorem preparedCircleInversionConstant_phaseFactor {r d : ℝ}
    (hr : 0 < r) (hd : 0 < d) :
    preparedCircleInversionConstant * (Real.sqrt r : ℂ) * preparedCirclePhaseFactor (r * d) =
      (Real.sqrt d : ℂ)⁻¹ * Complex.exp (-((r * d : ℝ) : ℂ) * Complex.I) := by
  have hroot : (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * (Real.sqrt r : ℂ) *
      (Real.sqrt (2 * Real.pi / (r * d)) : ℂ) = (Real.sqrt d : ℂ)⁻¹ := by
    exact_mod_cast normalized_circular_square_root hr hd
  rw [preparedCircleInversionConstant, preparedCirclePhaseFactor]
  calc
    _ = ((Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * (Real.sqrt r : ℂ) *
        (Real.sqrt (2 * Real.pi / (r * d)) : ℂ)) *
        (Complex.exp (-((Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
          Complex.exp (-((r * d - Real.pi / 4 : ℝ) : ℂ) * Complex.I)) := by ring
    _ = _ := by
      rw [hroot, ← Complex.exp_add]
      congr 2
      push_cast
      ring

/-- The actual normalized pointwise difference has the exact source phase and distance
weight, with the genuine circle integrals from the finite inverse series. -/
theorem preparedInverseCircleSeries_normalized_difference {r d : ℝ}
    (hr : 0 < r) (hd : 0 < d) (T : ℕ) (α : ℝ) (B : ℝ → ℂ) (φ u : ℝ) :
    (Real.sqrt d : ℂ)⁻¹ * Complex.exp (-((r * d : ℝ) : ℂ) * Complex.I) * B φ -
      preparedCircleInversionConstant * (Real.sqrt r : ℂ) *
        preparedInverseCircleSeries T α B φ (r * d) u =
      -(preparedCircleInversionConstant * (Real.sqrt r : ℂ) *
        (preparedInverseCircleSeries T α B φ (r * d) u -
          preparedCirclePhaseFactor (r * d) * B φ)) := by
  rw [← preparedCircleInversionConstant_phaseFactor hr hd]
  ring

/-- Literal source (7.4), with a quantitative bound on the actual pointwise error. -/
theorem preparedInverseCircleSeries_normalized_approximation {T : ℕ} (hT : 1 ≤ T)
    {B : ℝ → ℂ} {A M α φ r d : ℝ} (hB : IsDerivativeRegular A M (6 * T) B)
    (hBs : ContDiff ℝ ∞ B) (hBP : Periodic B (2 * Real.pi))
    (hr : 0 < r) (hd : 0 < d) (hΛ : 1 ≤ r * d)
    (hφ : unitCircleOfAngle φ ∈ closedDirectionArc α (1 / 40)) (u : ℝ)
    {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1 / 2)
    (hscale : 800 * (2 * T) * M ^ 2 * (r * d)⁻¹ ≤ q) :
    ‖(Real.sqrt d : ℂ)⁻¹ * Complex.exp (-((r * d : ℝ) : ℂ) * Complex.I) * B φ -
      preparedCircleInversionConstant * (Real.sqrt r : ℂ) *
        preparedInverseCircleSeries T α B φ (r * d) u‖ ≤
      (Real.sqrt d)⁻¹ * (2 * A * (2 * T + 1) * q ^ T +
        2 * A * circularStationaryRemainderBase T (1200 * (T : ℝ) ^ 2 + M) *
          (circularStationaryRemainderBase T (1200 * (T : ℝ) ^ 2 + M) / (r * d)) ^ T) := by
  have h := preparedInverseCircleSeries_approximation hT hB hBs hBP hΛ hφ u
    hq₀ hq₁ hscale
  have hw : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt r := by positivity
  rw [preparedInverseCircleSeries_normalized_difference hr hd, norm_neg, norm_mul,
    norm_mul, norm_preparedCircleInversionConstant, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg r)]
  calc
    _ ≤ ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt r) *
        (Real.sqrt (2 * Real.pi / (r * d)) * (2 * A * (2 * T + 1) * q ^ T) +
          2 * A * Real.sqrt (2 * Real.pi / (r * d)) *
            circularStationaryRemainderBase T (1200 * (T : ℝ) ^ 2 + M) *
              (circularStationaryRemainderBase T (1200 * (T : ℝ) ^ 2 + M) / (r * d)) ^ T) :=
      mul_le_mul_of_nonneg_left h hw
    _ = _ := by
      rw [show ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt r) *
          (Real.sqrt (2 * Real.pi / (r * d)) * (2 * A * (2 * T + 1) * q ^ T) +
            2 * A * Real.sqrt (2 * Real.pi / (r * d)) *
              circularStationaryRemainderBase T (1200 * (T : ℝ) ^ 2 + M) *
                (circularStationaryRemainderBase T (1200 * (T : ℝ) ^ 2 + M) / (r * d)) ^ T) =
          ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt r *
            Real.sqrt (2 * Real.pi / (r * d))) *
            (2 * A * (2 * T + 1) * q ^ T +
              2 * A * circularStationaryRemainderBase T (1200 * (T : ℝ) ^ 2 + M) *
                (circularStationaryRemainderBase T (1200 * (T : ℝ) ^ 2 + M) / (r * d)) ^ T)
          by ring, normalized_circular_square_root hr hd]

end FalconerThetaGauge
