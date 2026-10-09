module

public import FalconerThetaGauge.OrthogonalityKernelRadialPhase

/-! # The literal two-pair kernel has source decay when the center radial link fails -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function

namespace FalconerThetaGauge

open GaugeFrostman

theorem norm_orthogonalityTwoPairKernel_radial_source {θ : ℝ} {N a p v : ℕ}
    (hpar : ParameterFacts θ N) (hv : v ≤ N)
    (hw : 10 * (tolerance θ N * N) ≤ (v : ℝ) - p)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    {X Y P P' Q Q' : Fin 2 → ℤ}
    (hP : dyadicCube p P ⊆ dyadicCube a X) (hP' : dyadicCube p P' ⊆ dyadicCube a X)
    (hQ : dyadicCube p Q ⊆ dyadicCube a Y) (hQ' : dyadicCube p Q' ⊆ dyadicCube a Y)
    {x x' y y' : Plane} (hx : x ∈ dyadicCube p P) (hx' : x' ∈ dyadicCube p P')
    (hy : y ∈ dyadicCube p Q) (hy' : y' ∈ dyadicCube p Q')
    (i j : Fin (angularPartitionCount (orthogonalityArcScale a p (tolerance θ N * N))))
    (hfail : orthogonalityLinkThreshold p (tolerance θ N * N) <
      |inner ℝ (unitCircleOfAngle (equalAngularCellCenter _ i) : Plane)
          (dyadicCellCenter p P - dyadicCellCenter p P') +
        inner ℝ (unitCircleOfAngle (equalAngularCellCenter _ j) : Plane)
          (dyadicCellCenter p Q - dyadicCellCenter p Q')|) :
    ‖orthogonalityTwoPairKernel (8 * expansionCount θ N) v
      (orthogonalityArcScale a p (tolerance θ N * N)) i j b₁ b₂ x x' y y'‖ ≤
        64 * (4 : ℝ) ^ v * (2 * orthogonalityArcScale a p (tolerance θ N * N)) ^ 2 *
          (2 : ℝ) ^ (-(90 * (N : ℝ))) := by
  have hE : 0 ≤ tolerance θ N * N := by have := hpar.2.2.1.1; linarith
  have hlarge : 12 ≤ (2 : ℝ) ^ (tolerance θ N * N / 2) := by
    have he := hpar.2.2.1.1
    exact (by norm_num : (12 : ℝ) ≤ 2 ^ (8 : ℝ)).trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
  have hh := norm_orthogonalityTwoPairKernel_le_of_radial_cancel
    (8 * expansionCount θ N) v (orthogonalityArcScale_pos _ _ _)
    (orthogonalityArcScale_le_one _ _ _) (by positivity) i j hb₁ hb₂ hbound₁ hbound₂
    x x' y y' (q := (2 : ℝ) ^ (-(300 * (N : ℝ)))) (by
      intro w₁ w₂ hw₁ hw₂
      exact norm_integral_orthogonalityRadialAmplitude_le_terminal hpar hv hw (by omega)
        (orthogonality_radialPhase_gt_half_of_center_failure hE hlarge _ hP hP' hQ hQ'
          hx hx' hy hy' i j hw₁ hw₂ hfail).le)
  have hq : (2 : ℝ) ^ (-(300 * (N : ℝ))) ≤ (2 : ℝ) ^ (-(90 * (N : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have hpref : 1 ≤ 64 * (4 : ℝ) ^ v := by
    have h := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4) (n := v)
    nlinarith
  calc
    _ ≤ _ := hh
    _ ≤ (2 * orthogonalityArcScale a p (tolerance θ N * N)) ^ 2 *
        (2 : ℝ) ^ (-(90 * (N : ℝ))) :=
      mul_le_mul_of_nonneg_left hq (sq_nonneg _)
    _ ≤ _ := by
      simpa only [mul_assoc, one_mul] using mul_le_mul_of_nonneg_right hpref
        (by positivity : 0 ≤ (2 * orthogonalityArcScale a p (tolerance θ N * N)) ^ 2 *
          (2 : ℝ) ^ (-(90 * (N : ℝ))))

end FalconerThetaGauge
