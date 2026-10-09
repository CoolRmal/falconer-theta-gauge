module

public import FalconerThetaGauge.StationaryCircularInversionTerminal

/-! # Source §7.5 Step 1 with the actual normalized phase and terminal error -/

@[expose] public section

noncomputable section

open Function
open scoped ContDiff

namespace FalconerThetaGauge

/-- The actual prepared inverse circle integrals satisfy source (7.4) with error
at most `R⁻²⁰⁰`. The hypotheses are the numerical symbol and geometry bounds of
Step 0, rather than an assumed stationary expansion or inversion conclusion. -/
theorem preparedInverseCircleSeries_source_error {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) {B : ℝ → ℂ} {M α φ r d w : ℝ}
    (hB : IsDerivativeRegular 1 M (6 * expansionCount θ N) B)
    (hBs : ContDiff ℝ ∞ B) (hBP : Periodic B (2 * Real.pi))
    (hr : 0 < r) (hd : 0 < d)
    (hφ : unitCircleOfAngle φ ∈ closedDirectionArc α (1 / 40)) (u : ℝ)
    (hw : 10 * (tolerance θ N * N) ≤ w)
    (hΛ : (2 : ℝ) ^ (w - 4) ≤ r * d)
    (hMfrequency : M ≤ 256 * (expansionCount θ N : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1) *
      (2 : ℝ) ^ (w / 2 - (tolerance θ N * N) / 2))
    (hMterminal : M ≤ 256 * (expansionCount θ N : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1) *
      (2 : ℝ) ^ ((N : ℝ) - tolerance θ N * N))
    (hdterminal : (2 : ℝ) ^ (-(N : ℝ) - 4) ≤ d) :
    ‖(Real.sqrt d : ℂ)⁻¹ * Complex.exp (-((r * d : ℝ) : ℂ) * Complex.I) * B φ -
      preparedCircleInversionConstant * (Real.sqrt r : ℂ) *
        preparedInverseCircleSeries (expansionCount θ N) α B φ (r * d) u‖ ≤
      (2 : ℝ) ^ (-(200 * (N : ℝ))) := by
  let T := expansionCount θ N
  let E := tolerance θ N * N
  let q := (2 : ℝ) ^ (-(7 * E / 8))
  let Q := circularStationaryRemainderBase T (1200 * (T : ℝ) ^ 2 + M)
  have hN : 0 < N := by have := hpar.1; omega
  have hT : 1 ≤ T := Nat.ceil_pos.mpr (by have := tolerance_pos θ hN; positivity)
  have hE₀ : 0 ≤ E := by dsimp [E]; positivity [tolerance_pos θ hN]
  have hE : 16 ≤ E := hpar.2.2.1.1
  have hEN : E ≤ (N : ℝ) := by
    simpa only [E, one_mul] using
      mul_le_mul_of_nonneg_right (parameterFacts_tolerance_le_one hpar) (Nat.cast_nonneg N)
  have hΛ₁ : 1 ≤ r * d := (Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2)
    (by linarith : 0 ≤ w - 4)).trans hΛ
  have hq₀ : 0 ≤ q := by positivity
  have hq₁ : q ≤ 1 / 2 := stationary_decay_ratio_le_half hE
  have hM₀ : 0 ≤ M := by linarith [hB.one_le_scale]
  have hratio : Q / (r * d) ≤ q :=
    prepared_stationary_remainder_ratio_le hT hE₀ hw hM₀ hMfrequency hΛ hpar.2.1
  have hscale : 800 * (2 * T) * M ^ 2 * (r * d)⁻¹ ≤ q := by
    calc
      _ = (800 * (2 * T) * M ^ 2) / (r * d) := by ring
      _ ≤ Q / (r * d) := div_le_div_of_nonneg_right
        (stationary_inverse_scale_le_remainder hM₀) (le_of_lt (mul_pos hr hd))
      _ ≤ q := hratio
  have hQ₀ : 0 ≤ Q := circularStationaryRemainderBase_nonneg _ _
  have hQ : Q ≤ (2 : ℝ) ^ (2 * (N : ℝ)) :=
    prepared_stationary_remainder_le_terminal hE₀ hEN hM₀ hMterminal hpar.2.1
  have h := preparedInverseCircleSeries_normalized_approximation hT hB hBs hBP hr hd
    hΛ₁ hφ u hq₀ hq₁ hscale
  calc
    _ ≤ (Real.sqrt d)⁻¹ * (2 * (2 * (T : ℝ) + 1) * q ^ T +
        2 * Q * (Q / (r * d)) ^ T) := by simpa only [one_mul, mul_one] using h
    _ ≤ (Real.sqrt d)⁻¹ * (2 * (2 * (T : ℝ) + 1) * q ^ T + 2 * Q * q ^ T) := by
      gcongr
    _ ≤ _ := normalized_stationary_error_le_terminal_power (by have := hpar.1; omega)
      hQ₀ hq₀ (inverse_sqrt_distance_le_terminal hpar.1 hdterminal)
      (stationary_order_le_terminal_of_parameters hpar) hQ
      (stationary_decay_ratio_pow_le_of_parameters hpar)

end FalconerThetaGauge
