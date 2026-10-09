module

public import FalconerThetaGauge.SpaceSplittingCircleProductRemainder

/-! # The literal far circular product remainder has source R⁻³⁹⁰ decay -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FalconerThetaGauge

theorem norm_spaceSplittingAveragedCircleKernel_sub_stationaryProduct_le_source
    {ρ : Measure Plane} {θ : ℝ} {N L v K : ℕ} (hpar : ParameterFacts θ N)
    {width : ℝ} (I : Finset ProfileScheduleTest) (hcard : I.card ≤ N ^ 2 + 1)
    (hL : L ≤ N) (hlength : ∀ test ∈ I, test.length ≤ L)
    (hv : v ≤ N) (hK : 6 ≤ K) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ (tolerance θ N * N) width
      (8 * expansionCount θ N) I (2 * expansionCount θ N))
    (hb₂ : b₂ ∈ scheduledSymbolClass ρ (tolerance θ N * N) width
      (8 * expansionCount θ N) I (2 * expansionCount θ N))
    {h : ℝ} {x x' y y' : Plane}
    (hgap : 2 * max (L : ℝ) (tolerance θ N * N) ≤ (v : ℝ) - h)
    (hdx : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ dist x x')
    (hdy : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ dist y y') :
    ‖spaceSplittingAveragedCircleKernel b₁ b₂ K v x x' y y' -
      ∫ r : ℝ, orthogonalityRadialAmplitude K v r *
        spaceSplittingStationaryMain (expansionCount θ N) b₁ r x x' *
          spaceSplittingStationaryMain (expansionCount θ N) b₂ r y y'‖ ≤
      (2 : ℝ) ^ (-390 * (N : ℝ)) := by
  let T := expansionCount θ N
  let E := tolerance θ N * N
  let δ := (2 : ℝ) ^ (-400 * (N : ℝ))
  have hm₁ := measurable_of_mem_scheduledSymbolClass ρ E width (8 * T) I (2 * T) hb₁
  have hm₂ := measurable_of_mem_scheduledSymbolClass ρ E width (8 * T) I (2 * T) hb₂
  have hbound₁ := abs_le_one_of_mem_scheduledSymbolClass ρ E width (8 * T) I
    (by omega : 2 * T ≤ 8 * T) hb₁
  have hbound₂ := abs_le_one_of_mem_scheduledSymbolClass ρ E width (8 * T) I
    (by omega : 2 * T ≤ 8 * T) hb₂
  have hex : ∀ᵐ r ∂maskedFourierRadialMeasure K v,
      ‖spaceSplittingCircleIntegral b₁ r x x' -
        spaceSplittingStationaryMain T b₁ r x x'‖ ≤ δ := by
    filter_upwards [ae_maskedFourierRadialMeasure_window K v] with r hr
    apply norm_spaceSplittingCircleIntegral_sub_stationary_le_source hpar I hcard
      hL hlength hb₁ hgap _ hdx
    simpa only [Real.rpow_natCast] using hr.1
  have hey : ∀ᵐ r ∂maskedFourierRadialMeasure K v,
      ‖spaceSplittingCircleIntegral b₂ r y y' -
        spaceSplittingStationaryMain T b₂ r y y'‖ ≤ δ := by
    filter_upwards [ae_maskedFourierRadialMeasure_window K v] with r hr
    apply norm_spaceSplittingCircleIntegral_sub_stationary_le_source hpar I hcard
      hL hlength hb₂ hgap _ hdy
    simpa only [Real.rpow_natCast] using hr.1
  have hδ : 0 ≤ δ := by positivity
  have hδ₁ : δ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have hN : (4 : ℝ) ≤ N := by exact_mod_cast hpar.1
  have hc : 4 * Real.pi + δ ≤ 17 := by linarith [Real.pi_lt_four]
  have hpow : (4 : ℝ) ^ v ≤ (2 : ℝ) ^ (2 * (N : ℝ)) := by
    calc
      _ = (2 : ℝ) ^ (2 * (v : ℝ)) := by
        rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast,
          show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by exact_mod_cast Nat.mul_le_mul_left 2 hv)
  have herror := norm_averaged_circle_product_sub_stationary_product_le hm₁ hm₂
    hbound₁ hbound₂ K v T x x' y y' hδ hex hey
  apply herror.trans
  calc
    _ ≤ (64 * (4 : ℝ) ^ v) * 17 * δ := mul_le_mul_of_nonneg_right
      (mul_le_mul (maskedFourierRadialMeasure_real_univ_le hK v) hc
        (by positivity) (by positivity)) hδ
    _ ≤ (2 : ℝ) ^ (11 : ℝ) * (2 : ℝ) ^ (2 * (N : ℝ)) * δ := by
      have h := mul_le_mul_of_nonneg_right hpow (by positivity : (0 : ℝ) ≤ 64 * 17 * δ)
      have hc' : (64 : ℝ) * 17 ≤ (2 : ℝ) ^ (11 : ℝ) := by norm_num
      calc
        _ ≤ (64 * 17) * (2 : ℝ) ^ (2 * (N : ℝ)) * δ := by nlinarith [h]
        _ ≤ _ := by
          convert mul_le_mul_of_nonneg_right hc'
            (by positivity : 0 ≤ (2 : ℝ) ^ (2 * (N : ℝ)) * δ) using 1 <;> ring
    _ = (2 : ℝ) ^ (11 - 398 * (N : ℝ)) := by
      dsimp [δ]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

end FalconerThetaGauge
