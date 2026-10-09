module

public import FalconerThetaGauge.DirectionalTestsWideningGeometry
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! # Exact arc-length bounds for literal small-cosine direction bands -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

/-- Jordan's inequality on each half of a semicircle. -/
theorem two_div_pi_mul_abs_sub_half_pi_le_abs_cos {t : ℝ}
    (ht : t ∈ Icc 0 Real.pi) :
    2 / Real.pi * |t - Real.pi / 2| ≤ |Real.cos t| := by
  by_cases h : Real.pi / 2 ≤ t
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have hs := Real.mul_le_sin (x := t - Real.pi / 2) (by linarith) (by linarith [ht.2])
    rw [Real.sin_sub_pi_div_two] at hs
    exact hs.trans (neg_le_abs _)
  · rw [abs_of_nonpos (by linarith : t - Real.pi / 2 ≤ 0)]
    have hs := Real.mul_le_sin (x := Real.pi / 2 - t) (by linarith) (by linarith [ht.1])
    rw [Real.sin_pi_div_two_sub] at hs
    convert hs.trans (le_abs_self _) using 1
    ring

/-- The literal small-cosine band is covered by the two correct arcs in one period. -/
theorem small_cosine_band_subset {s : ℝ} (_hs : 0 ≤ s) :
    Ioc (-Real.pi) Real.pi ∩ {t : ℝ | |Real.cos t| ≤ s} ⊆
      Icc (-Real.pi / 2 - Real.pi * s / 2) (-Real.pi / 2 + Real.pi * s / 2) ∪
      Icc (Real.pi / 2 - Real.pi * s / 2) (Real.pi / 2 + Real.pi * s / 2) := by
  rintro t ⟨ht, hcos⟩
  by_cases h : 0 ≤ t
  · right
    have hbound := (two_div_pi_mul_abs_sub_half_pi_le_abs_cos ⟨h, ht.2⟩).trans hcos
    have hb : 2 * |t - Real.pi / 2| ≤ s * Real.pi := by
      apply (div_le_iff₀ Real.pi_pos).mp
      convert hbound using 1
      ring
    have ha : |t - Real.pi / 2| ≤ Real.pi * s / 2 := by nlinarith
    obtain ⟨hlo, hhi⟩ := abs_le.mp ha
    constructor <;> linarith
  · left
    have hbound := two_div_pi_mul_abs_sub_half_pi_le_abs_cos
      (t := -t) (by constructor <;> linarith [ht.1])
    rw [Real.cos_neg] at hbound
    have hb : 2 * |(-t) - Real.pi / 2| ≤ s * Real.pi := by
      apply (div_le_iff₀ Real.pi_pos).mp
      convert hbound.trans hcos using 1
      ring
    have ha : |(-t) - Real.pi / 2| ≤ Real.pi * s / 2 := by nlinarith
    obtain ⟨hlo, hhi⟩ := abs_le.mp ha
    constructor <;> linarith

/-- Exactly `2π min(1,s)` bounds the arc length of a small-cosine band. -/
theorem volume_small_cosine_band_le {s : ℝ} (hs : 0 ≤ s) :
    volume (Ioc (-Real.pi) Real.pi ∩ {t : ℝ | |Real.cos t| ≤ s}) ≤
      ENNReal.ofReal (2 * Real.pi * min 1 s) := by
  by_cases hs1 : 1 ≤ s
  · rw [min_eq_left hs1]
    calc
      _ ≤ volume (Ioc (-Real.pi) Real.pi) := measure_mono inter_subset_left
      _ = _ := by rw [Real.volume_Ioc]; congr 1; ring
  · rw [min_eq_right (le_of_not_ge hs1)]
    calc
      _ ≤ volume (Icc (-Real.pi / 2 - Real.pi * s / 2) (-Real.pi / 2 + Real.pi * s / 2) ∪
          Icc (Real.pi / 2 - Real.pi * s / 2) (Real.pi / 2 + Real.pi * s / 2)) :=
        measure_mono (small_cosine_band_subset hs)
      _ ≤ volume (Icc (-Real.pi / 2 - Real.pi * s / 2) (-Real.pi / 2 + Real.pi * s / 2)) +
          volume (Icc (Real.pi / 2 - Real.pi * s / 2) (Real.pi / 2 + Real.pi * s / 2)) :=
        measure_union_le _ _
      _ = _ := by
        rw [Real.volume_Icc, Real.volume_Icc,
          show (-Real.pi / 2 + Real.pi * s / 2) -
            (-Real.pi / 2 - Real.pi * s / 2) = Real.pi * s by ring,
          show (Real.pi / 2 + Real.pi * s / 2) -
            (Real.pi / 2 - Real.pi * s / 2) = Real.pi * s by ring,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- Translating a periodic integrand preserves its integral over a full angular period. -/
theorem intervalIntegral_periodic_comp_sub {f : ℝ → ℝ}
    (hf : Periodic f (2 * Real.pi)) (a : ℝ) :
    (∫ t in -Real.pi..Real.pi, f (t - a)) = ∫ t in -Real.pi..Real.pi, f t := by
  rw [intervalIntegral.integral_comp_sub_right]
  convert hf.intervalIntegral_add_eq (-Real.pi - a) (-Real.pi) using 1 <;>
    congr 1 <;> ring

/-- Indicators integrate to the literal band length in an oriented positive interval. -/
theorem real_volume_band_eq_intervalIntegral {a b : ℝ} (hab : a ≤ b) {S : Set ℝ}
    (hS : MeasurableSet S) :
    volume.real (Ioc a b ∩ S) = ∫ t in a..b, S.indicator (fun _ ↦ (1 : ℝ)) t := by
  rw [intervalIntegral.integral_of_le hab, integral_indicator_const _ hS]
  simp only [Measure.real, Measure.restrict_apply hS, inter_comm, smul_eq_mul, mul_one]

/-- Exact rotation invariance of a literal cosine band over the source angular period. -/
theorem volume_shifted_cosine_band_eq (a s : ℝ) :
    volume (Ioc (-Real.pi) Real.pi ∩ {t : ℝ | |Real.cos (t - a)| ≤ s}) =
      volume (Ioc (-Real.pi) Real.pi ∩ {t : ℝ | |Real.cos t| ≤ s}) := by
  let S : Set ℝ := {t | |Real.cos t| ≤ s}
  have hS : MeasurableSet S := (isClosed_le Real.continuous_cos.abs continuous_const).measurableSet
  have hSa : MeasurableSet {t : ℝ | |Real.cos (t - a)| ≤ s} := by
    exact (isClosed_le (Real.continuous_cos.comp (continuous_id.sub continuous_const)).abs
      continuous_const).measurableSet
  have hperiod : Periodic (S.indicator (fun _ ↦ (1 : ℝ))) (2 * Real.pi) := by
    intro t
    simp only [S, indicator, mem_ofPred_eq, Real.cos_add_two_pi]
  have hfun : (fun t ↦ {t : ℝ | |Real.cos (t - a)| ≤ s}.indicator (fun _ ↦ (1 : ℝ)) t) =
      fun t ↦ S.indicator (fun _ ↦ (1 : ℝ)) (t - a) := by
    ext t
    simp only [S, indicator, mem_ofPred_eq]
  have hreal : volume.real (Ioc (-Real.pi) Real.pi ∩ {t : ℝ | |Real.cos (t - a)| ≤ s}) =
      volume.real (Ioc (-Real.pi) Real.pi ∩ S) := by
    rw [real_volume_band_eq_intervalIntegral (by linarith [Real.pi_pos]) hSa,
      real_volume_band_eq_intervalIntegral (by linarith [Real.pi_pos]) hS, hfun]
    exact intervalIntegral_periodic_comp_sub hperiod a
  have hfinite : ∀ T : Set ℝ, volume (Ioc (-Real.pi) Real.pi ∩ T) ≠ ⊤ := by
    intro T
    exact ne_top_of_le_ne_top (by simp [Real.volume_Ioc]) (measure_mono inter_subset_left)
  exact (ENNReal.toReal_eq_toReal_iff' (hfinite _) (hfinite _)).mp hreal

/-- The same exact source band bound holds around every direction. -/
theorem volume_shifted_cosine_band_le (a : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    volume (Ioc (-Real.pi) Real.pi ∩ {t : ℝ | |Real.cos (t - a)| ≤ s}) ≤
      ENNReal.ofReal (2 * Real.pi * min 1 s) := by
  rw [volume_shifted_cosine_band_eq]
  exact volume_small_cosine_band_le hs

end FalconerThetaGauge
