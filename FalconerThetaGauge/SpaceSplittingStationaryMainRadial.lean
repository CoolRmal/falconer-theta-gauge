module

public import FalconerThetaGauge.SpaceSplittingStationaryMainPhases
public import FalconerThetaGauge.OrthogonalityRadialAmplitude

/-! # The literal integrable radial terms of both stationary signs -/

@[expose] public section

noncomputable section

open MeasureTheory Finset

namespace FalconerThetaGauge

def spaceSplittingStationaryRadialTerm (K v j k : ℕ) (dx dy : ℝ)
    (c c' : ℂ) (δ r : ℝ) : ℂ :=
  (c / (dx : ℂ) ^ j) * (c' / (dy : ℂ) ^ k) *
    (Complex.exp (-((r * δ : ℝ) : ℂ) * Complex.I) *
      spaceSplittingRadialAmplitude K v (1 - (j : ℤ) - k) r)

theorem integrable_spaceSplittingStationaryRadialTerm (K v j k : ℕ) (dx dy : ℝ)
    (c c' : ℂ) (δ : ℝ) :
    Integrable (spaceSplittingStationaryRadialTerm K v j k dx dy c c' δ) := by
  have he : Continuous (fun r : ℝ ↦ Complex.exp (-((r * δ : ℝ) : ℂ) * Complex.I)) := by
    fun_prop
  have hi := (he.mul (contDiff_spaceSplittingRadialAmplitude K v
    (1 - (j : ℤ) - k)).continuous).integrable_of_hasCompactSupport (μ := volume)
      ((hasCompactSupport_spaceSplittingRadialAmplitude K v (1 - (j : ℤ) - k)).mul_left)
  exact hi.const_mul _

theorem integral_spaceSplittingStationaryRadialTerm (K v j k : ℕ) (dx dy : ℝ)
    (c c' : ℂ) (δ : ℝ) :
    (∫ r : ℝ, spaceSplittingStationaryRadialTerm K v j k dx dy c c' δ r) =
      (c / (dx : ℂ) ^ j) * (c' / (dy : ℂ) ^ k) *
        spaceSplittingRadialMoment K v (1 - (j : ℤ) - k) δ := by
  unfold spaceSplittingStationaryRadialTerm spaceSplittingRadialMoment
  rw [integral_const_mul]

theorem spaceSplitting_stationary_radial_prefactor {r dx dy : ℝ}
    (hr : 0 < r) (hx : 0 < dx) (hy : 0 < dy) (K v j k : ℕ) :
    orthogonalityRadialAmplitude K v r *
        (Real.sqrt (2 * Real.pi / (r * dx)) : ℂ) *
        (Real.sqrt (2 * Real.pi / (r * dy)) : ℂ) *
        ((r * dx : ℝ) : ℂ)⁻¹ ^ j * ((r * dy : ℝ) : ℂ)⁻¹ ^ k =
      (2 * Real.pi / Real.sqrt (dx * dy) : ℝ) /
        (dx : ℂ) ^ j / (dy : ℂ) ^ k *
        spaceSplittingRadialAmplitude K v (1 - (j : ℤ) - k) r := by
  have hp : (Real.sqrt (2 * Real.pi / (r * dx)) : ℂ) *
      (Real.sqrt (2 * Real.pi / (r * dy)) : ℂ) * (r : ℂ) =
      (2 * Real.pi / Real.sqrt (dx * dy) : ℝ) := by
    exact_mod_cast spaceSplitting_stationary_prefactor hr hx hy
  calc
    _ = ((Real.sqrt (2 * Real.pi / (r * dx)) : ℂ) *
          (Real.sqrt (2 * Real.pi / (r * dy)) : ℂ) * (r : ℂ)) *
        ((r : ℂ) * ((r * dx : ℝ) : ℂ)⁻¹ ^ j * ((r * dy : ℝ) : ℂ)⁻¹ ^ k) *
        ((((2 : ℝ) ^ v)⁻¹ : ℂ) *
          (maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) : ℂ)) := by
      unfold orthogonalityRadialAmplitude
      ring
    _ = _ := by
      rw [hp, spaceSplitting_stationary_radial_power hr.ne']
      unfold spaceSplittingRadialAmplitude
      ring

def spaceSplittingEqualSignRadialSeries (K v T : ℕ) (dx dy : ℝ)
    (Gx Gy : ℝ → ℂ) (φx φy : ℝ) : ℂ :=
  (2 * Real.pi / Real.sqrt (dx * dy) : ℝ) *
    ∑ j ∈ range T, ∑ k ∈ range T,
      (Complex.I *
        (stationaryPhaseOperator j Gx φx / (dx : ℂ) ^ j) *
        (stationaryPhaseOperator k Gy φy / (dy : ℂ) ^ k) *
          spaceSplittingRadialMoment K v (1 - (j : ℤ) - k) (dx + dy) -
       Complex.I *
        (stationaryPhaseConjugateOperator j Gx (φx + Real.pi) / (dx : ℂ) ^ j) *
        (stationaryPhaseConjugateOperator k Gy (φy + Real.pi) / (dy : ℂ) ^ k) *
          spaceSplittingRadialMoment K v (1 - (j : ℤ) - k) (-(dx + dy)))

end FalconerThetaGauge
