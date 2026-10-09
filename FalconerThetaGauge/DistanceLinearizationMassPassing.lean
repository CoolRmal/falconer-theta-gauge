module

public import FalconerThetaGauge.DistanceLinearizationMassProjection
public import FalconerThetaGauge.DistanceLinearizationPassing

/-! # The genuine one-cell mass bound from actual passing and the actual profile height -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal RealInnerProductSpace

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- The exact one-cell coefficient in Estimate 7.7. -/
def linearizationCellCoefficient (ρ : Measure Plane) (θ : ℝ) (N p t : ℕ) : ℝ :=
  (2 : ℝ) ^ (-((t : ℝ) - p)) * (2 : ℝ) ^ ((N : ℝ) *
    (profileHeight (regularMeasureExcess ρ N) p p t + 6 * tolerance θ N))

theorem linearizationCellCoefficient_pos (ρ : Measure Plane) (θ : ℝ) (N p t : ℕ) :
    0 < linearizationCellCoefficient ρ θ N p t := by
  unfold linearizationCellCoefficient
  positivity

/-- A literal retained passing witness gives the manuscript's actual one-cell-pair mass bound. -/
theorem scalarCollisionMass_crossDistance_cells_le_height (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {θ : ℝ} {N a p t : ℕ}
    (hpar : ParameterFacts θ N) (hreg : IsRegularThrough (tolerance θ N) N ρ)
    {A B P Q : Fin 2 → ℤ} (hsep : SeparatedDyadicCells a A B)
    (hP : dyadicCube p P ⊆ dyadicCube a A) (hQ : dyadicCube p Q ⊆ dyadicCube a B)
    (hpt : p ≤ t) (ht : t ≤ N) (hdepth : a + t < 2 * p)
    {width width' : ℝ} (hwidth' : 1 ≤ width')
    (hgap : 8 * (2 : ℝ) ^ (-(tolerance θ N * N)) ≤ width - width')
    (hQmass : 0 < unitCellWeight ρ p Q) {x₀ y₀ : Plane}
    (hx₀ : x₀ ∈ dyadicCube p P) (hy₀ : y₀ ∈ dyadicCube p Q)
    (hw₀ : pairDirection x₀ y₀ ∈
      projectionPassingDirections ρ p t (tolerance θ N * N) width Q) :
    scalarCollisionMass
        (crossDistanceMeasure (ρ.restrict (dyadicCube p P)) (ρ.restrict (dyadicCube p Q)))
        (crossDistanceMeasure (ρ.restrict (dyadicCube p P)) (ρ.restrict (dyadicCube p Q)))
        ((2 : ℝ) ^ (-(t : ℝ))) 0 ≤
      4 * ENNReal.ofReal (linearizationCellCoefficient ρ θ N p t) *
        (ρ (dyadicCube p P)) ^ (2 : ℕ) * (ρ (dyadicCube p Q)) ^ (2 : ℕ) := by
  have hE : 2 ≤ (2 : ℝ) ^ (2 * (tolerance θ N * N)) := by
    calc
      (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by linarith [hpar.2.2.1.1])
  have hcount := retained_center_projection_count_le_height ρ hρ hpar hreg hsep hP hQ
    hpt ht hdepth hwidth' hgap hQmass hx₀ hy₀ hw₀
  exact (scalarCollisionMass_crossDistance_cells_le_four_count ρ hsep hP hQ hdepth
    hQmass hE).trans (by
      exact mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl
        (ENNReal.ofReal_le_ofReal hcount)) le_rfl) le_rfl)

/-- The same actual mass estimate in the real normalization used in Definition 7.2. -/
theorem real_scalarCollisionMass_crossDistance_cells_le_height (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {θ : ℝ} {N a p t : ℕ}
    (hpar : ParameterFacts θ N) (hreg : IsRegularThrough (tolerance θ N) N ρ)
    {A B P Q : Fin 2 → ℤ} (hsep : SeparatedDyadicCells a A B)
    (hP : dyadicCube p P ⊆ dyadicCube a A) (hQ : dyadicCube p Q ⊆ dyadicCube a B)
    (hpt : p ≤ t) (ht : t ≤ N) (hdepth : a + t < 2 * p)
    {width width' : ℝ} (hwidth' : 1 ≤ width')
    (hgap : 8 * (2 : ℝ) ^ (-(tolerance θ N * N)) ≤ width - width')
    (hQmass : 0 < unitCellWeight ρ p Q) {x₀ y₀ : Plane}
    (hx₀ : x₀ ∈ dyadicCube p P) (hy₀ : y₀ ∈ dyadicCube p Q)
    (hw₀ : pairDirection x₀ y₀ ∈
      projectionPassingDirections ρ p t (tolerance θ N * N) width Q) :
    (scalarCollisionMass
        (crossDistanceMeasure (ρ.restrict (dyadicCube p P)) (ρ.restrict (dyadicCube p Q)))
        (crossDistanceMeasure (ρ.restrict (dyadicCube p P)) (ρ.restrict (dyadicCube p Q)))
        ((2 : ℝ) ^ (-(t : ℝ))) 0).toReal ≤
      4 * linearizationCellCoefficient ρ θ N p t *
        unitCellWeight ρ p P ^ (2 : ℕ) * unitCellWeight ρ p Q ^ (2 : ℕ) := by
  have h := scalarCollisionMass_crossDistance_cells_le_height ρ hρ hpar hreg hsep hP hQ
    hpt ht hdepth hwidth' hgap hQmass hx₀ hy₀ hw₀
  have hreal := ENNReal.toReal_mono (by finiteness) h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (linearizationCellCoefficient_pos ρ θ N p t).le,
    unitCellWeight, measureReal_def] using hreal

end FalconerThetaGauge
