module

public import FalconerThetaGauge.SpaceSplittingEqualSignSeries
public import FalconerThetaGauge.SpaceSplittingOppositeSupport

/-! # The actual double stationary main has the passing distance-collision bound -/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace FalconerThetaGauge

theorem norm_spaceSplittingStationaryMain_product_integral_le_source
    (ρ : Measure Plane) [IsFiniteMeasure ρ] {θ : ℝ} {N L v levels : ℕ}
    (hpar : ParameterFacts θ N) (hlevels : 0 < levels)
    (hsize : (levels : ℝ) ≤ (2 : ℝ) ^ (tolerance θ N * N) / 8) (i : ℕ)
    (I : Finset ProfileScheduleTest) (hcard : I.card ≤ N ^ 2 + 1)
    (hordered : ScheduledTestsOrdered I) (hv : v ≤ N) {h : ℝ} (hh : h ≤ N)
    (hgap : 2 * max (L : ℝ) (tolerance θ N * N) ≤ (v : ℝ) - h)
    (hlength : ∀ test ∈ I, test.length ≤ L) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ (tolerance θ N * N)
      (directionalLevelWidth levels i) (8 * expansionCount θ N) I (2 * expansionCount θ N))
    (hb₂ : b₂ ∈ scheduledSymbolClass ρ (tolerance θ N * N)
      (directionalLevelWidth levels i) (8 * expansionCount θ N) I (2 * expansionCount θ N))
    {x x' y y' : Plane}
    (hdx : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ dist x x')
    (hdy : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ dist y y') :
    ‖∫ r : ℝ, orthogonalityRadialAmplitude (8 * expansionCount θ N) v r *
      spaceSplittingStationaryMain (expansionCount θ N) b₁ r x x' *
      spaceSplittingStationaryMain (expansionCount θ N) b₂ r y y'‖ ≤
      ((2 : ℝ) ^ (25 : ℕ) * (2 : ℝ) ^ v / Real.sqrt (dist x x' * dist y y') /
        (1 + (2 : ℝ) ^ v * |dist x x' - dist y y'|) ^ 2) *
      (scheduledPassingPairSet ρ ρ (tolerance θ N * N)
        (directionalLevelWidth levels (i + 1)) I I).indicator (fun _ ↦ (1 : ℝ)) (x, x') *
      (scheduledPassingPairSet ρ ρ (tolerance θ N * N)
        (directionalLevelWidth levels (i + 1)) I I).indicator (fun _ ↦ (1 : ℝ)) (y, y') +
      (2 : ℝ) ^ (-390 * (N : ℝ)) := by
  have hT : 1 ≤ expansionCount θ N := Nat.ceil_pos.mpr
    (by have := tolerance_pos θ (N := N) (by have := hpar.1; omega); positivity)
  have hx : 0 < dist x x' := lt_of_lt_of_le (by positivity) hdx
  have hy : 0 < dist y y' := lt_of_lt_of_le (by positivity) hdy
  have he := integral_orthogonalityRadialAmplitude_mul_stationaryMain_product
    (8 * expansionCount θ N) v (expansionCount θ N) b₁ b₂ x x' y y' hx hy
  change (∫ r : ℝ, orthogonalityRadialAmplitude (8 * expansionCount θ N) v r *
      spaceSplittingStationaryMain (expansionCount θ N) b₁ r x x' *
      spaceSplittingStationaryMain (expansionCount θ N) b₂ r y y') =
    spaceSplittingBuiltOppositeSeries (8 * expansionCount θ N) v
      (expansionCount θ N) b₁ b₂ x x' y y' +
    spaceSplittingBuiltEqualSignSeries (8 * expansionCount θ N) v
      (expansionCount θ N) b₁ b₂ x x' y y' at he
  rw [he]
  apply (norm_add_le _ _).trans
  exact add_le_add
    (norm_spaceSplittingBuiltOppositeSeries_le_passing_kernel ρ (tolerance θ N * N)
      hlevels hsize i (by omega) I hordered hlength hb₁ hb₂ hx hy
      (by simpa only [Real.rpow_natCast] using
        spaceSplitting_coefficient_scale_le_quarter hpar I hcard hgap hdx)
      (by simpa only [Real.rpow_natCast] using
        spaceSplitting_coefficient_scale_le_quarter hpar I hcard hgap hdy))
    (norm_spaceSplittingBuiltEqualSignSeries_le_source hpar I hcard hv hh hgap hlength
      hb₁ hb₂ hdx hdy)

end FalconerThetaGauge
