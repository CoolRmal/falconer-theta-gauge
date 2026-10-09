module

public import FalconerThetaGauge.SpaceSplittingCaseAMainBound
public import FalconerThetaGauge.SpaceSplittingCircleRemainderIntegral
public import FalconerThetaGauge.SpaceSplittingSpatialKernelBounds

/-! # Source Estimate 7.8 Case A for the actual averaged circular kernel -/

@[expose] public section

noncomputable section

open MeasureTheory Function

namespace FalconerThetaGauge

theorem spaceSplitting_integrated_stationary_error_le_terminal {N v : ℕ}
    (hN : 4 ≤ N) (hv : v ≤ N) :
    64 * (4 : ℝ) ^ v * (2 * Real.pi * (2 : ℝ) ^ (-400 * (N : ℝ))) ≤
      (2 : ℝ) ^ (-395 * (N : ℝ)) := by
  have hp : (4 : ℝ) ^ v ≤ (2 : ℝ) ^ (2 * (N : ℝ)) := by
    have he : (4 : ℝ) ^ v = ((2 : ℝ) ^ v) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm v 2, pow_mul]
      norm_num
    rw [he]
    calc
      _ ≤ ((2 : ℝ) ^ N) ^ 2 := pow_le_pow_left₀ (by positivity)
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hv) _
      _ = _ := by
        rw [← Real.rpow_natCast (2 : ℝ) N, ← Real.rpow_mul_natCast (by norm_num)]
        congr 1
        ring
  have hc : 128 * Real.pi ≤ (2 : ℝ) ^ (3 * (N : ℝ)) := by
    calc
      _ ≤ (2 : ℝ) ^ (12 : ℝ) := by nlinarith [Real.pi_lt_four]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by have hn : (4 : ℝ) ≤ N := by exact_mod_cast hN
            linarith)
  calc
    _ = (128 * Real.pi * (4 : ℝ) ^ v) * (2 : ℝ) ^ (-400 * (N : ℝ)) := by ring
    _ ≤ ((2 : ℝ) ^ (3 * (N : ℝ)) * (2 : ℝ) ^ (2 * (N : ℝ))) *
        (2 : ℝ) ^ (-400 * (N : ℝ)) := mul_le_mul_of_nonneg_right
      (mul_le_mul hc hp (by positivity) (by positivity)) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

theorem norm_spaceSplittingAveragedCircleKernel_caseA_le_source
    {ρ : Measure Plane} {θ : ℝ} {N L v : ℕ} (hpar : ParameterFacts θ N)
    {width : ℝ} (I : Finset ProfileScheduleTest) (hcard : I.card ≤ N ^ 2 + 1)
    (hL : L ≤ N) (hlength : ∀ test ∈ I, test.length ≤ L) (hv : v ≤ N)
    {h : ℝ} (hh : h ≤ N)
    (hgap : 2 * max (L : ℝ) (tolerance θ N * N) ≤ (v : ℝ) - h)
    {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ (tolerance θ N * N) width
      (8 * expansionCount θ N) I (2 * expansionCount θ N))
    (hb₂ : Measurable (uncurry b₂)) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    (x x' y y' : Plane) (hd : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ dist x x')
    (hfar : 2 * dist y y' < dist x x') :
    ‖spaceSplittingAveragedCircleKernel b₁ b₂ (8 * expansionCount θ N) v x x' y y'‖ ≤
      (2 : ℝ) ^ (-300 * (N : ℝ)) := by
  rw [spaceSplittingAveragedCircleKernel_eq_full_line]
  let F := ∫ r : ℝ, orthogonalityRadialAmplitude (8 * expansionCount θ N) v r *
    spaceSplittingCircleIntegral b₁ r x x' * spaceSplittingCircleIntegral b₂ r y y'
  let G := ∫ r : ℝ, orthogonalityRadialAmplitude (8 * expansionCount θ N) v r *
    spaceSplittingStationaryMain (expansionCount θ N) b₁ r x x' *
      spaceSplittingCircleIntegral b₂ r y y'
  have he : ‖F - G‖ ≤ (2 : ℝ) ^ (-395 * (N : ℝ)) :=
    (norm_integral_spaceSplittingCircle_sub_main_le_source hpar I hcard hL hlength hgap
      hb₁ hb₂ hbound₂ x x' y y' hd).trans
        (spaceSplitting_integrated_stationary_error_le_terminal hpar.1 hv)
  have hm : ‖G‖ ≤ (2 : ℝ) ^ (-390 * (N : ℝ)) :=
    norm_integral_spaceSplittingStationaryMain_caseA_le_source hpar I hcard hlength hv hh
      hgap hb₁ hb₂ hbound₂ x x' y y' hd hfar
  have hN₀ : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hR : 2 ≤ (2 : ℝ) ^ (N : ℝ) := by
    calc
      _ = (2 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by have hn : (4 : ℝ) ≤ N := by exact_mod_cast hpar.1
            linarith)
  change ‖F‖ ≤ _
  calc
    _ ≤ ‖F - G‖ + ‖G‖ := by
      simpa only [sub_add_cancel] using norm_add_le (F - G) G
    _ ≤ (2 : ℝ) ^ (-395 * (N : ℝ)) + (2 : ℝ) ^ (-390 * (N : ℝ)) := add_le_add he hm
    _ ≤ 2 * (2 : ℝ) ^ (-390 * (N : ℝ)) := by
      have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (show -395 * (N : ℝ) ≤ -390 * N by linarith)
      linarith
    _ ≤ (2 : ℝ) ^ (N : ℝ) * (2 : ℝ) ^ (-390 * (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hR (by positivity)
    _ = (2 : ℝ) ^ (-389 * (N : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

end FalconerThetaGauge
