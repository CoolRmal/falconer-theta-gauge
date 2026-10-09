module

public import FalconerThetaGauge.SpaceSplittingStationaryMainRadial

/-! # Exact four-sign expansion of the two actual circular stationary mains -/

@[expose] public section

noncomputable section

open MeasureTheory Finset

namespace FalconerThetaGauge

theorem spaceSplittingStationaryMain_eq_sum (T : ℕ) (b : Plane → UnitCircle → ℝ)
    (r : ℝ) (x x' : Plane) :
    spaceSplittingStationaryMain T b r x x' =
      (Real.sqrt (2 * Real.pi / (r * dist x x')) : ℂ) *
        ∑ j ∈ range T, ((r * dist x x' : ℝ) : ℂ)⁻¹ ^ j *
          (Complex.exp (-((r * dist x x' - Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
            stationaryPhaseOperator j (builtSymbolPairAngularAmplitude b b x x')
              (radialAngle 0 (x - x')) +
           Complex.exp (((r * dist x x' - Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
            stationaryPhaseConjugateOperator j (builtSymbolPairAngularAmplitude b b x x')
              (radialAngle 0 (x - x') + Real.pi)) := by
  unfold spaceSplittingStationaryMain
  simp only [mul_add, sum_add_distrib, mul_sum]
  congr 1 <;> apply sum_congr rfl <;> intros <;> ring

theorem spaceSplitting_stationary_product_term {r dx dy : ℝ}
    (hr : 0 < r) (hx : 0 < dx) (hy : 0 < dy) (K v j k : ℕ)
    (cx cx' cy cy' : ℂ) :
    orthogonalityRadialAmplitude K v r *
        (Real.sqrt (2 * Real.pi / (r * dx)) : ℂ) *
        (Real.sqrt (2 * Real.pi / (r * dy)) : ℂ) *
        (((r * dx : ℝ) : ℂ)⁻¹ ^ j *
          (Complex.exp (-((r * dx - Real.pi / 4 : ℝ) : ℂ) * Complex.I) * cx +
           Complex.exp (((r * dx - Real.pi / 4 : ℝ) : ℂ) * Complex.I) * cx')) *
        (((r * dy : ℝ) : ℂ)⁻¹ ^ k *
          (Complex.exp (-((r * dy - Real.pi / 4 : ℝ) : ℂ) * Complex.I) * cy +
           Complex.exp (((r * dy - Real.pi / 4 : ℝ) : ℂ) * Complex.I) * cy')) =
      (2 * Real.pi / Real.sqrt (dx * dy) : ℝ) *
        (spaceSplittingStationaryRadialTerm K v j k dx dy cx cy' (dx - dy) r +
         spaceSplittingStationaryRadialTerm K v k j dy dx cy cx' (dy - dx) r +
         Complex.I * spaceSplittingStationaryRadialTerm K v j k dx dy cx cy (dx + dy) r -
         Complex.I * spaceSplittingStationaryRadialTerm K v j k dx dy cx' cy'
           (-(dx + dy)) r) := by
  have hm : 1 - (k : ℤ) - j = 1 - (j : ℤ) - k := by omega
  calc
    _ = (orthogonalityRadialAmplitude K v r *
          (Real.sqrt (2 * Real.pi / (r * dx)) : ℂ) *
          (Real.sqrt (2 * Real.pi / (r * dy)) : ℂ) *
          ((r * dx : ℝ) : ℂ)⁻¹ ^ j * ((r * dy : ℝ) : ℂ)⁻¹ ^ k) *
        (Complex.exp (-((r * dx - Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
            Complex.exp (-((r * dy - Real.pi / 4 : ℝ) : ℂ) * Complex.I) * cx * cy +
         Complex.exp (-((r * dx - Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((r * dy - Real.pi / 4 : ℝ) : ℂ) * Complex.I) * cx * cy' +
         Complex.exp (-((r * dy - Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((r * dx - Real.pi / 4 : ℝ) : ℂ) * Complex.I) * cy * cx' +
         Complex.exp (((r * dx - Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((r * dy - Real.pi / 4 : ℝ) : ℂ) * Complex.I) * cx' * cy') := by
      ring
    _ = _ := by
      rw [spaceSplitting_stationary_radial_prefactor hr hx hy,
        spaceSplitting_stationary_phase_equal_positive,
        spaceSplitting_stationary_phase_opposite,
        spaceSplitting_stationary_phase_opposite,
        spaceSplitting_stationary_phase_equal_negative]
      unfold spaceSplittingStationaryRadialTerm
      rw [hm]
      ring

end FalconerThetaGauge
