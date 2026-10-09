/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularFilteredMeasureShellEstimate
public import FalconerThetaGauge.FourierReconstruction

/-! # The actual shell energies have the summability required for reconstruction -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Asymptotics
open scoped Classical

namespace FalconerThetaGauge

theorem summable_dyadic_gain_power (θ c : ℝ) (hθ : 0 < θ) (hc : 0 < c) :
    Summable (fun N : ℕ ↦ (2 : ℝ) ^ (-c * gain θ N * N)) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs := summable_exp_neg_mul_nat_rpow θ (Real.log 2 * c * gainCoefficient θ)
    hθ (mul_pos (mul_pos hlog hc) (gainCoefficient_pos θ))
  apply summable_of_isBigO_nat hs
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNpos : 0 < N := by omega
  have heq : (2 : ℝ) ^ (-c * gain θ N * N) =
      Real.exp (-(Real.log 2 * c * gainCoefficient θ) * (N : ℝ) ^ θ) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hgain := gain_mul_scale θ hNpos
    congr 1
    rw [show Real.log 2 * (-c * gain θ N * N) =
      -(Real.log 2 * c) * (gain θ N * N) by ring, hgain]
    ring
  rw [heq]
  simp only [one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact le_rfl

theorem dyadicMeasureFourierEnergy_eq_scalarFourierAnnulusIntegral
    (η : Measure ℝ) (N : ℕ) :
    dyadicMeasureFourierEnergy η N =
      scalarFourierAnnulusIntegral η ((N : ℝ) - 1) ((N : ℝ) + 1) := by
  have hlo : (2 : ℝ) ^ ((N : ℤ) - 1) = (2 : ℝ) ^ ((N : ℝ) - 1) := by
    rw [← Real.rpow_intCast]
    simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one]
  have hhi : (2 : ℝ) ^ ((N : ℤ) + 1) = (2 : ℝ) ^ ((N : ℝ) + 1) := by
    rw [← Real.rpow_intCast]
    simp only [Int.cast_add, Int.cast_natCast, Int.cast_one]
  unfold dyadicMeasureFourierEnergy scalarFourierAnnulusIntegral angularScalarFourier
  apply setIntegral_congr_set
  filter_upwards [volume.ae_ne ((2 : ℝ) ^ ((N : ℝ) - 1)),
    volume.ae_ne (-((2 : ℝ) ^ ((N : ℝ) - 1)))] with r hr₁ hr₂
  apply propext
  simp only [dyadicFrequencyShell, scalarFourierAnnulus, mem_ofPred_eq, hlo, hhi]
  have hne : |r| ≠ (2 : ℝ) ^ ((N : ℝ) - 1) := by
    intro he
    rcases le_total 0 r with hr | hr
    · exact hr₁ (by simpa only [abs_of_nonneg hr] using he)
    · exact hr₂ (by rw [abs_of_nonpos hr] at he; linarith)
  constructor
  · rintro ⟨hrlo, hrhi⟩
    exact ⟨lt_of_le_of_ne hrlo hne.symm, hrhi⟩
  · rintro ⟨hrlo, hrhi⟩
    exact ⟨hrlo.le, hrhi⟩

end FalconerThetaGauge
