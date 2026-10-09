module

public import FalconerThetaGauge.OrthogonalityAngularPhase

/-! # Actual unlinked angular cancellation with the true small-arc support factor -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff

namespace FalconerThetaGauge

open GaugeFrostman

theorem orthogonality_angular_nonstationary {ρ : Measure Plane} {T : ℕ} (hT : 1 ≤ T)
    {a p : ℕ} {E width : ℝ} (hE : 0 ≤ E) (hlarge : 12 ≤ (2 : ℝ) ^ (E / 2))
    {I : Finset ProfileScheduleTest} {L : ℕ} (hL : ∀ test ∈ I, test.length ≤ L)
    {b : Plane → UnitCircle → ℝ}
    (hb : b ∈ scheduledSymbolClass ρ E width (8 * T) I (2 * T))
    {X P P' : Fin 2 → ℤ} (hP : dyadicCube p P ⊆ dyadicCube a X)
    (hP' : dyadicCube p P' ⊆ dyadicCube a X) {x x' : Plane}
    (hx : x ∈ dyadicCube p P) (hx' : x' ∈ dyadicCube p P')
    (arc : Fin (angularPartitionCount (orthogonalityArcScale a p E)))
    (hfail : orthogonalityLinkThreshold p E <
      |inner ℝ (circleQuarterTurn (unitCircleOfAngle (equalAngularCellCenter _ arc)) : Plane)
        (dyadicCellCenter p P - dyadicCellCenter p P')|) {r : ℝ} (hr : 0 < r) :
    ‖∫ θ in (equalAngularCellCenter (angularPartitionCount (orthogonalityArcScale a p E)) arc -
        Real.pi)..(equalAngularCellCenter (angularPartitionCount (orthogonalityArcScale a p E))
          arc + Real.pi),
      Complex.exp ((orthogonalityAngularPhase r (x - x') θ : ℂ) * Complex.I) *
        orthogonalityAngularAmplitude (8 * T) (orthogonalityArcScale a p E) arc b x x' θ‖ ≤
      2 * orthogonalityArcScale a p E *
        (2 * (T + 1 : ℝ) ^ 2 * max (orthogonalityAngularScale T E I L a p)
          (3 * ‖x - x'‖ / orthogonalityLinkThreshold p E) /
            (r * orthogonalityLinkThreshold p E / 3)) ^ T := by
  let τ := orthogonalityLinkThreshold p E
  let ℓ := orthogonalityArcScale a p E
  let c := equalAngularCellCenter (angularPartitionCount ℓ) arc
  let A := orthogonalityAngularAmplitude (8 * T) ℓ arc b x x'
  let U := {θ : ℝ | τ / 3 < |inner ℝ
    (circleQuarterTurn (unitCircleOfAngle θ) : Plane) (x - x')|}
  have hτ : 0 < τ := mul_pos (dyadicRadius_pos p) (Real.rpow_pos_of_pos (by norm_num) _)
  have hcont : Continuous (fun θ ↦ |inner ℝ
      (circleQuarterTurn (unitCircleOfAngle θ) : Plane) (x - x')|) := by
    simp_rw [circleQuarterTurn_unitCircleOfAngle, coe_unitCircleOfAngle]
    exact ((continuous_angularDirection.comp (continuous_id.add continuous_const)).inner
      continuous_const).abs
  have hU : IsOpen U := isOpen_lt continuous_const hcont
  have hs : tsupport A ⊆ U := by
    intro θ hθ
    have hh := orthogonalityAngularAmplitude_support_perp_low hE hlarge (8 * T)
      hP hP' hx hx' arc b hfail θ hθ
    change τ / 3 < _
    change τ / 2 < _ at hh
    linarith
  have hlow : ∀ θ ∈ U, r * τ / 3 ≤ ‖deriv (orthogonalityAngularPhase r (x - x')) θ‖ := by
    intro θ hθ
    rw [deriv_orthogonalityAngularPhase, norm_mul, Real.norm_eq_abs, abs_neg, abs_of_pos hr,
      Real.norm_eq_abs]
    change τ / 3 < _ at hθ
    have hh := mul_le_mul_of_nonneg_left hθ.le hr.le
    linarith
  have hAP : Periodic A (2 * Real.pi) := by
    intro θ
    dsimp [A, orthogonalityAngularAmplitude]
    rw [unitCircleOfAngle_add_two_pi, periodic_builtSymbolPairAngularAmplitude]
  have hAs : ContDiff ℝ ∞ A :=
    (Complex.ofRealCLM.contDiff.comp
      (contDiff_equalArcCutoff_comp_angle (8 * T) (orthogonalityArcScale_pos a p E) arc)).mul
        (contDiff_builtSymbolPairAngularAmplitude hb hb x x')
  have hreg := orthogonalityAngularAmplitude_isDerivativeRegular hT hL hb arc x x'
  have h := nonstationary_phase_periodic_support
    (contDiff_orthogonalityAngularPhase r (x - x')) hAs Real.two_pi_pos.le
    (orthogonalityAngularPhase_periodic r (x - x')) hAP (c - Real.pi) hreg
    (by omega : T ≤ 6 * T) (by positivity : 0 < r * τ / 3)
    (mul_nonneg hr.le (norm_nonneg _)) hU hs hlow
    (fun j _ _ θ _ ↦ norm_iteratedDeriv_orthogonalityAngularPhase_le hr.le _ j θ)
  have hend : c - Real.pi + 2 * Real.pi = c + Real.pi := by ring
  have hratio : r * ‖x - x'‖ / (r * τ / 3) = 3 * ‖x - x'‖ / τ := by
    field_simp [hr.ne', hτ.ne']
  rw [hend, hratio] at h
  have hmass := orthogonalityAngularAmplitude_support_mass_le (8 * T)
    (orthogonalityArcScale_pos a p E) (orthogonalityArcScale_le_one a p E) arc b x x'
  exact h.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_right hmass
      (pow_nonneg (by positivity : 0 ≤ 2 * (T + 1 : ℝ) ^ 2 *
        max (orthogonalityAngularScale T E I L a p) (3 * ‖x - x'‖ / τ) / (r * τ / 3)) T))

end FalconerThetaGauge
