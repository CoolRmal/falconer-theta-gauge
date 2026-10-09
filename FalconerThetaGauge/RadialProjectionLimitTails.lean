module

public import FalconerThetaGauge.RadialProjectionLimit
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Analysis.PSeries

/-!
# Quantitative tails of the limiting Radon–Nikodym density

The open-set cutoff estimate gives a logarithmic tail bound for the actual
Radon–Nikodym derivative. These tails preserve lower logarithmic Orlicz
moments when the approximating densities have a stronger moment.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace FalconerThetaGauge

/-- Absorption of a half-sized finite mass, including an infinite error term. -/
theorem ennreal_le_two_mul_of_cutoff {a b T : ℝ≥0∞} (ha : a ≠ ∞)
    (hab : 2 * b ≤ a) (hcutoff : a ≤ b + T) : a ≤ 2 * T := by
  by_cases hT : T = ∞
  · simp [hT]
  have hb : b ≠ ∞ := by
    intro hb
    simp [hb] at hab
    exact ha hab
  apply (ENNReal.toReal_le_toReal ha (ENNReal.mul_ne_top (by simp) hT)).mp
  have hlow := (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (by simp) hb) ha).mpr hab
  have hupp := (ENNReal.toReal_le_toReal ha (ENNReal.add_ne_top.mpr ⟨hb, hT⟩)).mpr hcutoff
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_add hb hT] at *
  linarith

/-- The exact density tail following from the cutoff estimate. -/
theorem measure_density_tail_le {α : Type*} [MeasurableSpace α]
    (σ ξ : Measure α) [IsFiniteMeasure σ] {f : α → ℝ≥0∞}
    (hf : Measurable f) (hdensity : ξ.withDensity f = σ)
    {p : ℝ} {K : ℝ≥0∞}
    (hcutoff : ∀ H : ℝ, 0 < H → ∀ A : Set α,
      σ A ≤ ENNReal.ofReal H * ξ A + orliczTailCoefficient p H * K)
    {H : ℝ} (hH : 0 < H) :
    σ {x | ENNReal.ofReal (2 * H) < f x} ≤ 2 * (orliczTailCoefficient p H * K) := by
  let A : Set α := {x | ENNReal.ofReal (2 * H) < f x}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hf
  have hlow : 2 * (ENNReal.ofReal H * ξ A) ≤ σ A := by
    rw [← hdensity, withDensity_apply _ hA]
    calc
      2 * (ENNReal.ofReal H * ξ A) = ENNReal.ofReal (2 * H) * ξ A := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, mul_assoc]
      _ = ∫⁻ x in A, ENNReal.ofReal (2 * H) ∂ξ := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in A, f x ∂ξ := setLIntegral_mono' hA (fun x hx ↦ hx.le)
  exact ennreal_le_two_mul_of_cutoff (measure_ne_top σ A) hlow (hcutoff H hH A)

/-- The tail bound is for the genuine Radon–Nikodym derivative of the weak limit. -/
theorem measure_rnDeriv_tail_le {α : Type*} [MeasurableSpace α]
    (σ ξ : Measure α) [IsFiniteMeasure σ] [SigmaFinite ξ]
    (hac : σ ≪ ξ) {p : ℝ} {K : ℝ≥0∞}
    (hcutoff : ∀ H : ℝ, 0 < H → ∀ A : Set α,
      σ A ≤ ENNReal.ofReal H * ξ A + orliczTailCoefficient p H * K)
    {H : ℝ} (hH : 0 < H) :
    σ {x | ENNReal.ofReal (2 * H) < σ.rnDeriv ξ x} ≤
      2 * (orliczTailCoefficient p H * K) :=
  measure_density_tail_le σ ξ (Measure.measurable_rnDeriv σ ξ)
    (Measure.withDensity_rnDeriv_eq σ ξ hac) hcutoff hH

/-- At exponential cutoffs the logarithmic tail coefficient is polynomially small. -/
theorem orliczTailCoefficient_exp_le {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    orliczTailCoefficient p (Real.exp ((n : ℝ) + 1)) ≤
      ENNReal.ofReal (((n : ℝ) + 1) ^ (-p)) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlog : (n : ℝ) + 1 ≤ Real.log (Real.exp 1 + Real.exp ((n : ℝ) + 1)) := by
    calc
      (n : ℝ) + 1 = Real.log (Real.exp ((n : ℝ) + 1)) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _)
        (le_add_of_nonneg_left (Real.exp_nonneg 1))
  rw [orliczTailCoefficient, ← ENNReal.ofReal_inv_of_pos
    (Real.rpow_pos_of_pos (hn.trans_le hlog) p), Real.rpow_neg hn.le]
  exact ENNReal.ofReal_le_ofReal (inv_anti₀ (Real.rpow_pos_of_pos hn p)
    (Real.rpow_le_rpow hn.le hlog hp))

/-- The moment-loss majorant is summable with the two spare logarithmic powers. -/
theorem summable_orlicz_tail_majorant {γ : ℝ} (hγ : 0 ≤ γ) :
    Summable (fun n : ℕ ↦ ((n : ℝ) + 4) ^ γ * ((n : ℝ) + 1) ^ (-(γ + 2))) := by
  have hbase : Summable (fun n : ℕ ↦ ((n : ℝ) + 1) ^ (-2 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1))
  apply (hbase.mul_left ((4 : ℝ) ^ γ)).of_nonneg_of_le (fun n ↦ by positivity)
  intro n
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hpoly : ((n : ℝ) + 4) ^ γ ≤ (4 : ℝ) ^ γ * ((n : ℝ) + 1) ^ γ := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hn.le]
    apply Real.rpow_le_rpow (by positivity) _ hγ
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  calc
    _ ≤ ((4 : ℝ) ^ γ * ((n : ℝ) + 1) ^ γ) * ((n : ℝ) + 1) ^ (-(γ + 2)) := by gcongr
    _ = (4 : ℝ) ^ γ * ((n : ℝ) + 1) ^ (-2 : ℝ) := by
      rw [mul_assoc, ← Real.rpow_add hn]
      congr 2
      ring

end FalconerThetaGauge
