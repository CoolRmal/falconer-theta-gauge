module

public import FalconerThetaGauge.ScalarEnergyBinningKernel
public import FalconerThetaGauge.MaskedDistanceEnergyReal

/-! # The genuine collision-kernel integral in terms of actual weighted distance energies -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FalconerThetaGauge

theorem dyadic_scalar_kernel_toReal_le (η ζ : Measure ℝ)
    [IsFiniteMeasure η] [IsFiniteMeasure ζ] (v : ℕ) :
    (2 : ℝ) ^ v *
      (∫⁻ p, scalarBinningKernel ((2 : ℝ) ^ (-(v : ℝ))) p ∂η.prod ζ).toReal ≤
      10 * Real.sqrt (((2 : ℝ) ^ v *
        (scalarCollisionMass η η ((2 : ℝ) ^ (-(v : ℝ))) 0).toReal) *
          ((2 : ℝ) ^ v * (scalarCollisionMass ζ ζ ((2 : ℝ) ^ (-(v : ℝ))) 0).toReal)) := by
  have hs : 0 ≤ (2 : ℝ) ^ v := by positivity
  have h := ENNReal.toReal_mono (by unfold scalarCollisionMass; finiteness)
    (lintegral_scalarBinningKernel_le_ten η ζ (by positivity : 0 < (2 : ℝ) ^ (-(v : ℝ))))
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ← ENNReal.toReal_rpow,
    ENNReal.toReal_mul, ← Real.sqrt_eq_rpow] at h
  apply (mul_le_mul_of_nonneg_left h hs).trans_eq
  rw [show ((2 : ℝ) ^ v *
      (scalarCollisionMass η η ((2 : ℝ) ^ (-(v : ℝ))) 0).toReal) *
        ((2 : ℝ) ^ v * (scalarCollisionMass ζ ζ ((2 : ℝ) ^ (-(v : ℝ))) 0).toReal) =
      ((2 : ℝ) ^ v) ^ 2 *
        ((scalarCollisionMass η η ((2 : ℝ) ^ (-(v : ℝ))) 0).toReal *
          (scalarCollisionMass ζ ζ ((2 : ℝ) ^ (-(v : ℝ))) 0).toReal) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hs]
  ring

/-- Normalization of both literal collision measures, with no Fourier-energy hypothesis. -/
theorem dyadic_scalar_kernel_toReal_le_normalized (η ζ : Measure ℝ)
    [IsFiniteMeasure η] [IsFiniteMeasure ζ] {m n : ℝ} (hm : 0 < m) (hn : 0 < n)
    (v : ℕ) :
    (2 : ℝ) ^ v *
      (∫⁻ p, scalarBinningKernel ((2 : ℝ) ^ (-(v : ℝ))) p ∂η.prod ζ).toReal ≤
      10 * Real.sqrt ((m * normalizedDistanceCollisionEnergy η m v) *
        (n * normalizedDistanceCollisionEnergy ζ n v)) := by
  have heq (μ : Measure ℝ) (mass : ℝ) (hmass : mass ≠ 0) :
      mass * normalizedDistanceCollisionEnergy μ mass v =
        (2 : ℝ) ^ v * (scalarCollisionMass μ μ ((2 : ℝ) ^ (-(v : ℝ))) 0).toReal := by
    unfold normalizedDistanceCollisionEnergy
    rw [Real.rpow_natCast]
    field_simp
  rw [heq η m hm.ne', heq ζ n hn.ne']
  exact dyadic_scalar_kernel_toReal_le η ζ v

end FalconerThetaGauge
