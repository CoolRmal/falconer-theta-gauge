module

public import FalconerThetaGauge.RadialProjectionOrlicz
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform absolute continuity from stronger logarithmic moments

A bound for the actual extended Orlicz integral controls the mass of every
measurable set by its reference measure plus a tail term. The tail tends to
zero as the cutoff tends to infinity. This is the uniform-integrability
ingredient for the direct measure-limit proof of radial absolute continuity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace FalconerThetaGauge

/-- The explicit tail coefficient of the logarithmic Orlicz bound. -/
def orliczTailCoefficient (p H : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (Real.log (Real.exp 1 + H) ^ p))⁻¹

theorem orliczTailCoefficient_ne_top (p : ℝ) {H : ℝ} (hH : 0 ≤ H) :
    orliczTailCoefficient p H ≠ ∞ := by
  apply ENNReal.inv_ne_top.mpr
  exact (ENNReal.ofReal_pos.mpr
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le (log_exp_one_add_ge_one hH)) p)).ne'

/-- The high-density tail is controlled pointwise by the literal Orlicz function. -/
theorem le_cutoff_add_orlicz {p H : ℝ} (hp : 0 ≤ p) (hH : 0 < H) (t : ℝ≥0∞) :
    t ≤ ENNReal.ofReal H + orliczTailCoefficient p H * orliczPhiExtended p t := by
  by_cases hsmall : t ≤ ENNReal.ofReal H
  · exact hsmall.trans (le_add_of_nonneg_right (by positivity))
  by_cases ht : t = ∞
  · have hc : orliczTailCoefficient p H ≠ 0 :=
      ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
    simp [ht, ENNReal.mul_top, hc]
  have htH : H ≤ t.toReal := by
    have h := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top ht).mpr
      (not_le.mp hsmall).le
    simpa only [ENNReal.toReal_ofReal hH.le] using h
  have hlog : Real.log (Real.exp 1 + H) ≤ Real.log (Real.exp 1 + t.toReal) :=
    Real.log_le_log (by positivity) (add_le_add le_rfl htH)
  have hpow : Real.log (Real.exp 1 + H) ^ p ≤ Real.log (Real.exp 1 + t.toReal) ^ p :=
    Real.rpow_le_rpow (zero_le_one.trans (log_exp_one_add_ge_one hH.le)) hlog hp
  have hcostpos : 0 < Real.log (Real.exp 1 + H) ^ p :=
    Real.rpow_pos_of_pos (zero_lt_one.trans_le (log_exp_one_add_ge_one hH.le)) p
  have hcost : ENNReal.ofReal (Real.log (Real.exp 1 + H) ^ p) * t ≤
      orliczPhiExtended p t := by
    conv_lhs => rw [← ENNReal.ofReal_toReal ht]
    rw [← ENNReal.ofReal_mul hcostpos.le]
    simp only [orliczPhiExtended, ite_eq_right ht, orliczPhiENN, orliczPhi]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [ENNReal.toReal_nonneg (a := t)])
  have htail : t ≤ orliczTailCoefficient p H * orliczPhiExtended p t := by
    have h := mul_le_mul_right hcost (orliczTailCoefficient p H)
    simpa only [orliczTailCoefficient, ← mul_assoc,
      ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hcostpos).ne' ENNReal.ofReal_ne_top,
      one_mul] using h
  exact htail.trans (le_add_of_nonneg_left (by positivity))

/-- A genuine uniform absolute-continuity estimate for a measure given by a density. -/
theorem withDensity_le_cutoff_add_orlicz {α : Type*} [MeasurableSpace α]
    (ξ : Measure α) {f : α → ℝ≥0∞} {p H : ℝ}
    (hp : 0 ≤ p) (hH : 0 < H) {K : ℝ≥0∞}
    (hbound : (∫⁻ x, orliczPhiExtended p (f x) ∂ξ) ≤ K)
    {A : Set α} (hA : MeasurableSet A) :
    ξ.withDensity f A ≤ ENNReal.ofReal H * ξ A + orliczTailCoefficient p H * K := by
  rw [withDensity_apply _ hA]
  calc
    (∫⁻ x in A, f x ∂ξ) ≤
        ∫⁻ x in A, ENNReal.ofReal H + orliczTailCoefficient p H *
          orliczPhiExtended p (f x) ∂ξ :=
      lintegral_mono fun x ↦ le_cutoff_add_orlicz hp hH (f x)
    _ = ENNReal.ofReal H * ξ A + orliczTailCoefficient p H *
        ∫⁻ x in A, orliczPhiExtended p (f x) ∂ξ := by
      rw [lintegral_add_left measurable_const, setLIntegral_const,
        lintegral_const_mul' _ _ (orliczTailCoefficient_ne_top p hH.le)]
    _ ≤ ENNReal.ofReal H * ξ A + orliczTailCoefficient p H * K := by
      gcongr
      exact (setLIntegral_le_lintegral _ _).trans hbound

/-- A stronger logarithmic Orlicz moment makes the tail coefficient tend to zero. -/
theorem tendsto_orliczTailCoefficient {p : ℝ} (hp : 0 < p) :
    Tendsto (orliczTailCoefficient p) atTop (𝓝 0) := by
  have hlog : Tendsto (fun H : ℝ ↦ Real.log (Real.exp 1 + H)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_mono
      (fun H ↦ le_add_of_nonneg_left (Real.exp_nonneg 1)) tendsto_id)
  have hpow := (tendsto_rpow_atTop hp).comp hlog
  have hinv : Tendsto (fun H : ℝ ↦ (Real.log (Real.exp 1 + H) ^ p)⁻¹) atTop (𝓝 0) :=
    hpow.inv_tendsto_atTop
  have hENN := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hinv
  simp only [ENNReal.ofReal_zero] at hENN
  apply hENN.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
  exact ENNReal.ofReal_inv_of_pos
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le (log_exp_one_add_ge_one hH)) p)

end FalconerThetaGauge
