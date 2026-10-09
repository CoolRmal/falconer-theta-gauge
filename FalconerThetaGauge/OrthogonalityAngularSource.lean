module

public import FalconerThetaGauge.OrthogonalityAngularFrequency

/-! # The source R^-90 angular cancellation for the actual built symbols and cells -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FalconerThetaGauge

open GaugeFrostman

theorem orthogonality_angular_source_decay {ρ : Measure Plane} {θ : ℝ} {N a p v : ℕ}
    (hpar : ParameterFacts θ N) (hpv : p ≤ v)
    (hgap : (p : ℝ) - a ≤ (v : ℝ) - p + 2 * (tolerance θ N * N))
    {width : ℝ} {I : Finset ProfileScheduleTest} {L : ℕ}
    (hcard : I.card ≤ N ^ 2 + 1) (hL : ∀ test ∈ I, test.length ≤ L)
    (hlength : (L : ℝ) ≤ (v : ℝ) - p + 2 * (tolerance θ N * N))
    {b : Plane → UnitCircle → ℝ}
    (hb : b ∈ scheduledSymbolClass ρ (tolerance θ N * N) width
      (8 * expansionCount θ N) I (2 * expansionCount θ N))
    {X P P' : Fin 2 → ℤ} (hP : dyadicCube p P ⊆ dyadicCube a X)
    (hP' : dyadicCube p P' ⊆ dyadicCube a X) {x x' : Plane}
    (hx : x ∈ dyadicCube p P) (hx' : x' ∈ dyadicCube p P')
    (arc : Fin (angularPartitionCount (orthogonalityArcScale a p (tolerance θ N * N))))
    (hfail : orthogonalityLinkThreshold p (tolerance θ N * N) <
      |inner ℝ (circleQuarterTurn (unitCircleOfAngle (equalAngularCellCenter _ arc)) : Plane)
        (dyadicCellCenter p P - dyadicCellCenter p P')|)
    {r : ℝ} (hr : (2 : ℝ) ^ ((v : ℝ) - 2) ≤ r) :
    ‖∫ φ in (equalAngularCellCenter
        (angularPartitionCount (orthogonalityArcScale a p (tolerance θ N * N))) arc -
          Real.pi)..(equalAngularCellCenter
        (angularPartitionCount (orthogonalityArcScale a p (tolerance θ N * N))) arc + Real.pi),
      Complex.exp ((orthogonalityAngularPhase r (x - x') φ : ℂ) * Complex.I) *
        orthogonalityAngularAmplitude (8 * expansionCount θ N)
          (orthogonalityArcScale a p (tolerance θ N * N)) arc b x x' φ‖ ≤
      2 * orthogonalityArcScale a p (tolerance θ N * N) *
        (2 : ℝ) ^ (-(90 * (N : ℝ))) := by
  let T := expansionCount θ N
  let E := tolerance θ N * N
  let τ := orthogonalityLinkThreshold p E
  let Ma := orthogonalityAngularScale T E I L a p
  let F := (2 : ℝ) ^ ((v : ℝ) - p + E)
  have hN : 0 < N := by have := hpar.1; omega
  have hT : 1 ≤ T := Nat.ceil_pos.mpr (by have := tolerance_pos θ hN; positivity)
  have hE₁₆ : 16 ≤ E := hpar.2.2.1.1
  have hE : 0 ≤ E := by linarith
  have hlarge : 12 ≤ (2 : ℝ) ^ (E / 2) := by
    calc
      _ ≤ (2 : ℝ) ^ (8 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hr₀ : 0 < r := (Real.rpow_pos_of_pos (by norm_num) _).trans_le hr
  have hτ : 0 < τ := mul_pos (dyadicRadius_pos p) (Real.rpow_pos_of_pos (by norm_num) _)
  have hMa := orthogonalityAngularScale_le_frequency hT hE hpv hgap I hcard hlength
  have hq := orthogonalityAngularPhaseRatio_le_frequency hE hgap (hP hx) (hP' hx')
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hpoly : (5 : ℝ) ≤ 1024 * (T : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1) := by
    have ht : 1 ≤ (T : ℝ) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (N : ℝ)]
  have hq' : 3 * ‖x - x'‖ / τ ≤ 1024 * (T : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1) * F :=
    hq.trans (mul_le_mul_of_nonneg_right hpoly (by positivity))
  have hratio := orthogonality_angular_decay_ratio_le hMa hq'
    (orthogonalityAngularPhaseLambda_le_frequency hr) hpar.2.1
  have hbase₀ : 0 ≤ 2 * (T + 1 : ℝ) ^ 2 * max Ma (3 * ‖x - x'‖ / τ) / (r * τ / 3) := by
    have hq₀ : 0 ≤ 3 * ‖x - x'‖ / τ := by positivity
    have hmax : 0 ≤ max Ma (3 * ‖x - x'‖ / τ) := hq₀.trans (le_max_right _ _)
    positivity
  have hpow := (pow_le_pow_left₀ hbase₀ hratio T).trans
    (orthogonality_angular_decay_pow_le_of_parameters hpar)
  exact (orthogonality_angular_nonstationary hT hE hlarge hL hb hP hP' hx hx' arc
    hfail hr₀).trans (mul_le_mul_of_nonneg_left hpow
      (by have := orthogonalityArcScale_pos a p E; positivity))

end FalconerThetaGauge
