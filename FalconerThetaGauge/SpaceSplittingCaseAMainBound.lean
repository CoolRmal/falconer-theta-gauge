module

public import FalconerThetaGauge.SpaceSplittingCaseAMain

/-! # Uniform decay of the actual Case A finite stationary main integral -/

@[expose] public section

noncomputable section

open MeasureTheory Function Finset

namespace FalconerThetaGauge

theorem spaceSplitting_caseA_order_prefactor_le_terminal {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) :
    4 * Real.pi * expansionCount θ N ≤ (2 : ℝ) ^ (2 * (N : ℝ)) := by
  have ht := stationary_order_le_terminal_of_parameters hpar
  have hR : 4 ≤ (2 : ℝ) ^ (N : ℝ) := by
    calc
      _ ≤ (2 : ℝ) ^ (4 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by exact_mod_cast hpar.1)
  calc
    _ ≤ Real.pi * (2 : ℝ) ^ (N : ℝ) := by nlinarith [Real.pi_pos]
    _ ≤ (2 : ℝ) ^ (N : ℝ) * (2 : ℝ) ^ (N : ℝ) :=
      mul_le_mul_of_nonneg_right (Real.pi_lt_four.le.trans hR) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring

theorem norm_integral_spaceSplittingStationaryMain_caseA_le_source
    {ρ : Measure Plane} {θ : ℝ} {N L v : ℕ} (hpar : ParameterFacts θ N)
    {width : ℝ} (I : Finset ProfileScheduleTest) (hcard : I.card ≤ N ^ 2 + 1)
    (hlength : ∀ test ∈ I, test.length ≤ L) (hv : v ≤ N) {h : ℝ} (hh : h ≤ N)
    (hgap : 2 * max (L : ℝ) (tolerance θ N * N) ≤ (v : ℝ) - h)
    {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ (tolerance θ N * N) width
      (8 * expansionCount θ N) I (2 * expansionCount θ N))
    (hb₂ : Measurable (uncurry b₂)) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    (x x' y y' : Plane) (hd : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ dist x x')
    (hfar : 2 * dist y y' < dist x x') :
    ‖∫ r : ℝ, orthogonalityRadialAmplitude (8 * expansionCount θ N) v r *
      spaceSplittingStationaryMain (expansionCount θ N) b₁ r x x' *
        spaceSplittingCircleIntegral b₂ r y y'‖ ≤ (2 : ℝ) ^ (-390 * (N : ℝ)) := by
  have hd₀ : 0 < dist x x' := lt_of_lt_of_le (by positivity) hd
  rw [integral_spaceSplittingStationaryMain_circle_eq_sum _ _ _ b₁ hb₂ hbound₂ _ _ _ _ hd₀]
  have hterm (j : ℕ) (hj : j ∈ range (expansionCount θ N)) :
      ‖(∫ r : ℝ, spaceSplittingCaseAStationaryTerm (8 * expansionCount θ N) v j 1
          (dist x x') (stationaryPhaseOperator j (builtSymbolPairAngularAmplitude b₁ b₁ x x')
            (radialAngle 0 (x - x'))) r * spaceSplittingCircleIntegral b₂ r y y') +
        ∫ r : ℝ, spaceSplittingCaseAStationaryTerm (8 * expansionCount θ N) v j (-1)
          (dist x x') (stationaryPhaseConjugateOperator j
            (builtSymbolPairAngularAmplitude b₁ b₁ x x') (radialAngle 0 (x - x') + Real.pi)) r *
              spaceSplittingCircleIntegral b₂ r y y'‖ ≤
        4 * Real.pi * (2 : ℝ) ^ (-400 * (N : ℝ)) := by
    have hp := norm_integral_spaceSplittingCaseAStationaryTerm_circle_le_source hpar I hcard hv
      hh hgap hd (by norm_num : |(1 : ℝ)| = 1) (mem_range.1 hj)
      (norm_stationaryPhaseOperator_builtPair_le hlength hb₁ (mem_range.1 hj) x x'
        (radialAngle 0 (x - x')))
      hb₂ hbound₂ y y' hfar
    have hm := norm_integral_spaceSplittingCaseAStationaryTerm_circle_le_source hpar I hcard hv
      hh hgap hd (by norm_num : |(-1 : ℝ)| = 1) (mem_range.1 hj)
      (norm_stationaryPhaseConjugateOperator_builtPair_le hlength hb₁ (mem_range.1 hj) x x'
        (radialAngle 0 (x - x') + Real.pi))
      hb₂ hbound₂ y y' hfar
    exact (norm_add_le _ _).trans (add_le_add hp hm) |>.trans_eq (by ring)
  calc
    _ ≤ ∑ j ∈ range (expansionCount θ N),
        (4 * Real.pi * (2 : ℝ) ^ (-400 * (N : ℝ))) :=
      (norm_sum_le _ _).trans (sum_le_sum hterm)
    _ = (4 * Real.pi * expansionCount θ N) * (2 : ℝ) ^ (-400 * (N : ℝ)) := by simp; ring
    _ ≤ (2 : ℝ) ^ (2 * (N : ℝ)) * (2 : ℝ) ^ (-400 * (N : ℝ)) :=
      mul_le_mul_of_nonneg_right (spaceSplitting_caseA_order_prefactor_le_terminal hpar)
        (by positivity)
    _ = (2 : ℝ) ^ (-398 * (N : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by have := Nat.cast_nonneg (α := ℝ) N; linarith)

end FalconerThetaGauge
