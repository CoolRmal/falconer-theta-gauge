module

public import FalconerThetaGauge.SpaceSplittingCaseBMain
public import FalconerThetaGauge.SpaceSplittingCircleProductSource

/-! # The true averaged circular kernel has the Case B passing collision bound -/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace FalconerThetaGauge

theorem norm_spaceSplittingAveragedCircleKernel_caseB_le_source
    (ρ : Measure Plane) [IsFiniteMeasure ρ] {θ : ℝ} {N L v levels : ℕ}
    (hpar : ParameterFacts θ N) (hlevels : 0 < levels)
    (hsize : (levels : ℝ) ≤ (2 : ℝ) ^ (tolerance θ N * N) / 8) (i : ℕ)
    (I : Finset ProfileScheduleTest) (hcard : I.card ≤ N ^ 2 + 1)
    (hordered : ScheduledTestsOrdered I) (hL : L ≤ N) (hv : v ≤ N) {h : ℝ} (hh : h ≤ N)
    (hgap : 2 * max (L : ℝ) (tolerance θ N * N) ≤ (v : ℝ) - h)
    (hlength : ∀ test ∈ I, test.length ≤ L) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ (tolerance θ N * N)
      (directionalLevelWidth levels i) (8 * expansionCount θ N) I (2 * expansionCount θ N))
    (hb₂ : b₂ ∈ scheduledSymbolClass ρ (tolerance θ N * N)
      (directionalLevelWidth levels i) (8 * expansionCount θ N) I (2 * expansionCount θ N))
    {x x' y y' : Plane}
    (hdx : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ dist x x')
    (hdy : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ dist y y') :
    ‖spaceSplittingAveragedCircleKernel b₁ b₂ (8 * expansionCount θ N) v x x' y y'‖ ≤
      ((2 : ℝ) ^ (25 : ℕ) * (2 : ℝ) ^ v / Real.sqrt (dist x x' * dist y y') /
        (1 + (2 : ℝ) ^ v * |dist x x' - dist y y'|) ^ 2) *
      (scheduledPassingPairSet ρ ρ (tolerance θ N * N)
        (directionalLevelWidth levels (i + 1)) I I).indicator (fun _ ↦ (1 : ℝ)) (x, x') *
      (scheduledPassingPairSet ρ ρ (tolerance θ N * N)
        (directionalLevelWidth levels (i + 1)) I I).indicator (fun _ ↦ (1 : ℝ)) (y, y') +
      (2 : ℝ) ^ (-380 * (N : ℝ)) := by
  have hT : 1 ≤ expansionCount θ N := Nat.ceil_pos.mpr
    (by have := tolerance_pos θ (N := N) (by have := hpar.1; omega); positivity)
  have hrem := norm_spaceSplittingAveragedCircleKernel_sub_stationaryProduct_le_source
    hpar I hcard hL hlength hv (by omega : 6 ≤ 8 * expansionCount θ N)
    hb₁ hb₂ hgap hdx hdy
  have hmain := norm_spaceSplittingStationaryMain_product_integral_le_source ρ hpar
    hlevels hsize i I hcard hordered hv hh hgap hlength hb₁ hb₂ hdx hdy
  have htwo : 2 * (2 : ℝ) ^ (-390 * (N : ℝ)) ≤ (2 : ℝ) ^ (-380 * (N : ℝ)) := by
    calc
      _ = (2 : ℝ) ^ (1 - 390 * (N : ℝ)) := by
        nth_rw 1 [show (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) by norm_num]
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by have hn : (4 : ℝ) ≤ N := by exact_mod_cast hpar.1
            linarith)
  have hnorm := norm_add_le
    (spaceSplittingAveragedCircleKernel b₁ b₂ (8 * expansionCount θ N) v x x' y y' -
      ∫ r : ℝ, orthogonalityRadialAmplitude (8 * expansionCount θ N) v r *
        spaceSplittingStationaryMain (expansionCount θ N) b₁ r x x' *
        spaceSplittingStationaryMain (expansionCount θ N) b₂ r y y')
    (∫ r : ℝ, orthogonalityRadialAmplitude (8 * expansionCount θ N) v r *
      spaceSplittingStationaryMain (expansionCount θ N) b₁ r x x' *
      spaceSplittingStationaryMain (expansionCount θ N) b₂ r y y')
  rw [sub_add_cancel] at hnorm
  linarith

end FalconerThetaGauge
