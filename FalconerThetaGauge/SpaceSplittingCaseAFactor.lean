module

public import FalconerThetaGauge.SpaceSplittingCaseASource

/-! # The actual stationary radial term is exactly the real-power amplitude -/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace FalconerThetaGauge

theorem spaceSplitting_caseA_real_factor_eq {r d : ℝ} (hr : 0 < r) (hd : 0 < d)
    (j : ℕ) :
    r ^ (2 : ℕ) * Real.sqrt (2 * Real.pi / (r * d)) * (r * d)⁻¹ ^ j =
      Real.sqrt (2 * Real.pi / d) * d⁻¹ ^ j * r ^ ((3 / 2 : ℝ) - j) := by
  have hs : Real.sqrt (2 * Real.pi / (r * d)) =
      Real.sqrt (2 * Real.pi / d) / Real.sqrt r := by
    rw [show 2 * Real.pi / (r * d) = (2 * Real.pi / d) / r by ring,
      Real.sqrt_div (by positivity : 0 ≤ 2 * Real.pi / d)]
  have hp : r ^ (2 : ℕ) * (Real.sqrt r)⁻¹ * r⁻¹ ^ j = r ^ ((3 / 2 : ℝ) - j) := by
    have hi : r⁻¹ ^ j = r ^ (-(j : ℝ)) := by
      rw [inv_pow, Real.rpow_neg hr.le, Real.rpow_natCast]
    rw [hi, Real.sqrt_eq_rpow, ← Real.rpow_neg hr.le, ← Real.rpow_natCast]
    rw [← Real.rpow_add hr, ← Real.rpow_add hr]
    congr 1
    ring
  rw [hs, mul_inv, mul_pow]
  calc
    _ = Real.sqrt (2 * Real.pi / d) * d⁻¹ ^ j *
        (r ^ (2 : ℕ) * (Real.sqrt r)⁻¹ * r⁻¹ ^ j) := by ring
    _ = _ := by rw [hp]

/-- A literal single stationary contribution, including the actual dyadic radial weight. -/
def spaceSplittingCaseAStationaryTerm (K v j : ℕ) (σ d : ℝ) (c : ℂ) (r : ℝ) : ℂ :=
  orthogonalityRadialAmplitude K v r * (Real.sqrt (2 * Real.pi / (r * d)) : ℂ) *
    Complex.exp (-((σ * (r * d - Real.pi / 4) : ℝ) : ℂ) * Complex.I) *
      ((r * d : ℝ) : ℂ)⁻¹ ^ j * c

theorem spaceSplittingCaseAStationaryTerm_eq_realPower (K v j : ℕ) (σ d : ℝ)
    (c : ℂ) (hd : 0 < d) (r : ℝ) :
    spaceSplittingCaseAStationaryTerm K v j σ d c r =
      (Real.sqrt (2 * Real.pi / d) : ℂ) * (d : ℂ)⁻¹ ^ j * c *
        Complex.exp (((σ * Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
        (Complex.exp (-((r * (σ * d) : ℝ) : ℂ) * Complex.I) *
          spaceSplittingCaseAAmplitude K v j r) := by
  by_cases hr : 0 < r
  · have hf := congrArg (fun x : ℝ ↦ (x : ℂ)) (spaceSplitting_caseA_real_factor_eq hr hd j)
    have he : Complex.exp (-((σ * (r * d - Real.pi / 4) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((σ * Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
          Complex.exp (-((r * (σ * d) : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    unfold spaceSplittingCaseAStationaryTerm orthogonalityRadialAmplitude
      spaceSplittingCaseAAmplitude spaceSplittingRealPowerAmplitude
    push_cast at hf he ⊢
    rw [he]
    calc
      _ = ((((2 : ℝ) ^ v)⁻¹ : ℝ) : ℂ) *
          (maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) : ℂ) *
          ((r : ℂ) ^ 2 * (Real.sqrt (2 * Real.pi / (r * d)) : ℂ) *
            ((r : ℂ) * (d : ℂ))⁻¹ ^ j) * c *
          (Complex.exp (((σ * Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
            Complex.exp (-((r * (σ * d) : ℝ) : ℂ) * Complex.I)) := by push_cast; ring
      _ = _ := by rw [hf]; push_cast; ring
  · have hnot : r ∉ Icc ((2 : ℝ) ^ v / 4) (4 * (2 : ℝ) ^ v) := by
      intro hm
      exact hr (lt_of_lt_of_le (by positivity) hm.1)
    simp only [spaceSplittingCaseAStationaryTerm,
      orthogonalityRadialAmplitude_eq_zero K v hnot, zero_mul,
      spaceSplittingCaseAAmplitude, spaceSplittingRealPowerAmplitude_eq_zero K v _ hnot,
      mul_zero]

end FalconerThetaGauge
