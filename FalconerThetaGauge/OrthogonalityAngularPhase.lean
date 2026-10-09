module

public import FalconerThetaGauge.OrthogonalityAngularBudget
public import FalconerThetaGauge.OrthogonalityPhaseSeparation
public import FalconerThetaGauge.EqualArcSupportMeasure
public import FalconerThetaGauge.NonstationaryPhasePeriodicSupport

/-! # The genuine angular phase derivatives and support separation for unlinked cells -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff

namespace FalconerThetaGauge

open GaugeFrostman

def orthogonalityAngularPhase (r : ℝ) (z : Plane) : ℝ → ℝ :=
  fun θ ↦ -r * inner ℝ (angularDirection θ) z

theorem orthogonalityAngularPhase_zero (r : ℝ) :
    orthogonalityAngularPhase r 0 = fun _ ↦ 0 := by
  funext θ
  simp only [orthogonalityAngularPhase, inner_zero_right, mul_zero]

theorem orthogonalityAngularPhase_eq_circular (r : ℝ) {z : Plane} (hz : z ≠ 0) :
    orthogonalityAngularPhase r z = circularOscillatoryPhase (r * ‖z‖) (radialAngle 0 z) := by
  funext θ
  rw [orthogonalityAngularPhase, real_inner_comm z (angularDirection θ),
    inner_vector_angularDirection_eq z hz θ, circularOscillatoryPhase]
  ring

theorem contDiff_orthogonalityAngularPhase (r : ℝ) (z : Plane) :
    ContDiff ℝ ∞ (orthogonalityAngularPhase r z) := by
  by_cases hz : z = 0
  · rw [hz, orthogonalityAngularPhase_zero]
    exact contDiff_const
  · rw [orthogonalityAngularPhase_eq_circular r hz]
    exact contDiff_circularOscillatoryPhase _ _

theorem orthogonalityAngularPhase_periodic (r : ℝ) (z : Plane) :
    Periodic (orthogonalityAngularPhase r z) (2 * Real.pi) := by
  intro θ
  simp only [orthogonalityAngularPhase, angularDirection_add_two_pi]

theorem deriv_orthogonalityAngularPhase (r : ℝ) (z : Plane) (θ : ℝ) :
    deriv (orthogonalityAngularPhase r z) θ =
      -r * inner ℝ (circleQuarterTurn (unitCircleOfAngle θ) : Plane) z := by
  by_cases hz : z = 0
  · rw [hz, orthogonalityAngularPhase_zero]
    simp only [deriv_const, inner_zero_right, mul_zero]
  · rw [orthogonalityAngularPhase_eq_circular r hz, deriv_circularOscillatoryPhase,
      circleQuarterTurn_unitCircleOfAngle, coe_unitCircleOfAngle,
      real_inner_comm z (angularDirection (θ + Real.pi / 2)),
      inner_vector_angularDirection_eq z hz]
    rw [show θ + Real.pi / 2 - radialAngle 0 z =
      (θ - radialAngle 0 z) + Real.pi / 2 by ring, Real.cos_add_pi_div_two]
    ring

theorem norm_iteratedDeriv_orthogonalityAngularPhase_le {r : ℝ} (hr : 0 ≤ r)
    (z : Plane) (j : ℕ) (θ : ℝ) :
    ‖iteratedDeriv j (orthogonalityAngularPhase r z) θ‖ ≤ r * ‖z‖ := by
  by_cases hz : z = 0
  · rw [hz, orthogonalityAngularPhase_zero]
    simp only [iteratedDeriv_fun_const_zero, norm_zero, mul_zero, le_refl]
  · rw [orthogonalityAngularPhase_eq_circular r hz]
    exact norm_iteratedDeriv_circularOscillatoryPhase_le (mul_nonneg hr (norm_nonneg z)) _ j θ

theorem orthogonalityAngularAmplitude_support_subset (K : ℕ) {ℓ : ℝ}
    (arc : Fin (angularPartitionCount ℓ)) (b : Plane → UnitCircle → ℝ) (x x' : Plane) :
    tsupport (orthogonalityAngularAmplitude K ℓ arc b x x') ⊆
      tsupport (fun θ ↦ equalArcCutoff K ℓ arc (unitCircleOfAngle θ)) := by
  exact tsupport_mul_subset_left.trans
    (tsupport_comp_subset (g := fun t : ℝ ↦ (t : ℂ)) rfl _)

theorem orthogonalityAngularAmplitude_support_mass_le (K : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hℓ₁ : ℓ ≤ 1) (arc : Fin (angularPartitionCount ℓ))
    (b : Plane → UnitCircle → ℝ) (x x' : Plane) :
    volume.real (tsupport (orthogonalityAngularAmplitude K ℓ arc b x x') ∩
      Ioc (equalAngularCellCenter (angularPartitionCount ℓ) arc - Real.pi)
        (equalAngularCellCenter (angularPartitionCount ℓ) arc + Real.pi)) ≤ 2 * ℓ := by
  have hs := inter_subset_inter_left
    (Ioc (equalAngularCellCenter (angularPartitionCount ℓ) arc - Real.pi)
      (equalAngularCellCenter (angularPartitionCount ℓ) arc + Real.pi))
    (orthogonalityAngularAmplitude_support_subset K arc b x x')
  have hfinite : volume (tsupport (fun θ ↦ equalArcCutoff K ℓ arc (unitCircleOfAngle θ)) ∩
      Ioc (equalAngularCellCenter (angularPartitionCount ℓ) arc - Real.pi)
        (equalAngularCellCenter (angularPartitionCount ℓ) arc + Real.pi)) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_Ioc_lt_top.ne (measure_mono inter_subset_right)
  exact (ENNReal.toReal_mono hfinite (measure_mono hs)).trans
    (equalArcCutoff_support_period_mass_le K hℓ hℓ₁ arc)

theorem orthogonalityAngularAmplitude_support_perp_low {a p : ℕ} {E : ℝ}
    (hE : 0 ≤ E) (hlarge : 12 ≤ (2 : ℝ) ^ (E / 2)) (K : ℕ)
    {X P P' : Fin 2 → ℤ} (hP : dyadicCube p P ⊆ dyadicCube a X)
    (hP' : dyadicCube p P' ⊆ dyadicCube a X) {x x' : Plane}
    (hx : x ∈ dyadicCube p P) (hx' : x' ∈ dyadicCube p P')
    (arc : Fin (angularPartitionCount (orthogonalityArcScale a p E)))
    (b : Plane → UnitCircle → ℝ)
    (hfail : orthogonalityLinkThreshold p E <
      |inner ℝ (circleQuarterTurn (unitCircleOfAngle (equalAngularCellCenter _ arc)) : Plane)
        (dyadicCellCenter p P - dyadicCellCenter p P')|) :
    ∀ θ ∈ tsupport (orthogonalityAngularAmplitude K (orthogonalityArcScale a p E) arc b x x'),
      orthogonalityLinkThreshold p E / 2 <
        |inner ℝ (circleQuarterTurn (unitCircleOfAngle θ) : Plane) (x - x')| := by
  intro θ hθ
  have hs := orthogonalityAngularAmplitude_support_subset K arc b x x' hθ
  have hchord := equalArcCutoff_support_chord_le K (orthogonalityArcScale_pos a p E) arc hs
  have hdir : ‖(circleQuarterTurn (unitCircleOfAngle θ) : Plane) -
      (circleQuarterTurn (unitCircleOfAngle (equalAngularCellCenter _ arc)) : Plane)‖ ≤
      orthogonalityArcScale a p E := by
    change ‖planeQuarterTurn (unitCircleOfAngle θ : Plane) - planeQuarterTurn
      (unitCircleOfAngle (equalAngularCellCenter _ arc) : Plane)‖ ≤ _
    rw [norm_planeQuarterTurn_sub]
    change ‖angularDirection θ - angularDirection (equalAngularCellCenter _ arc)‖ ≤ _
    linarith [orthogonalityArcScale_pos a p E]
  have herr := dyadic_point_center_error hP hP' hx hx' hE
    (circleQuarterTurn (unitCircleOfAngle θ))
    (circleQuarterTurn (unitCircleOfAngle (equalAngularCellCenter _ arc))) hdir
  apply abs_gt_half_of_center_failure hfail (herr.trans _)
  have hhalf := orthogonality_phase_error_le_half (p := p) hlarge
  have hpos : 0 ≤ dyadicRadius p * (2 : ℝ) ^ E :=
    mul_nonneg (dyadicRadius_pos p).le (Real.rpow_pos_of_pos (by norm_num) E).le
  linarith

end FalconerThetaGauge
