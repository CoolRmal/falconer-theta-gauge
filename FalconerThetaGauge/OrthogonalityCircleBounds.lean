module

public import FalconerThetaGauge.OrthogonalityCircleKernel

/-! # Actual cutoff circle integrals retain the source small-arc factor -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped RealInnerProductSpace

namespace FalconerThetaGauge

theorem integral_norm_orthogonalityCircleKernel_le (K : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hℓ₁ : ℓ ≤ 1) (arc : Fin (angularPartitionCount ℓ))
    {b : Plane → UnitCircle → ℝ} (hb : Measurable (uncurry b))
    (hbound : ∀ x w, |b x w| ≤ 1) (x x' : Plane) (r : ℝ) :
    (∫ w, ‖orthogonalityCircleKernel K ℓ arc b x x' r w‖ ∂circleArcLength) ≤ 2 * ℓ := by
  let c := equalAngularCellCenter (angularPartitionCount ℓ) arc
  let f : ℝ → ℝ := fun t ↦ ‖orthogonalityCircleKernel K ℓ arc b x x' r
    (unitCircleOfAngle t)‖
  let S := tsupport (fun t ↦ equalArcCutoff K ℓ arc (unitCircleOfAngle t)) ∩
    Ioc (c - Real.pi) (c + Real.pi)
  have hf : ∀ t, ‖f t‖ ≤ 1 := by
    intro t
    simpa only [f, Real.norm_eq_abs, abs_norm] using
      norm_orthogonalityCircleKernel_le_one K hℓ arc hbound x x' r (unitCircleOfAngle t)
  have heq : (∫ t in Ioc (c - Real.pi) (c + Real.pi), f t) = ∫ t in S, f t := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc inter_subset_right
    intro t ht
    have hnot : t ∉ tsupport (fun t ↦ equalArcCutoff K ℓ arc (unitCircleOfAngle t)) :=
      fun h ↦ ht.2 ⟨h, ht.1⟩
    have hz : equalArcCutoff K ℓ arc (unitCircleOfAngle t) = 0 := by
      by_contra h
      exact hnot (subset_closure h)
    simp only [f, norm_orthogonalityCircleKernel K hℓ, hz, zero_mul]
  have hS : volume S < ⊤ := (measure_mono inter_subset_right).trans_lt (by simp)
  have hh := norm_setIntegral_le_of_norm_le_const hS (fun t _ ↦ hf t)
  rw [integral_circle_eq_interval
    ((measurable_orthogonalityCircleKernel K hℓ arc hb x x').of_uncurry_left.norm)
      (c - Real.pi),
    show c - Real.pi + 2 * Real.pi = c + Real.pi by ring,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : c - Real.pi ≤ c + Real.pi)]
  change (∫ t in Ioc (c - Real.pi) (c + Real.pi), f t) ≤ _
  rw [heq]
  have hmass : volume.real S ≤ 2 * ℓ := by
    simpa only [S, c] using equalArcCutoff_support_period_mass_le K hℓ hℓ₁ arc
  have habs : |∫ t in S, f t| ≤ volume.real S := by
    simpa only [Real.norm_eq_abs, one_mul] using hh
  exact (le_abs_self _).trans (habs.trans hmass)

theorem norm_integral_orthogonalityCircleKernel_le (K : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hℓ₁ : ℓ ≤ 1) (arc : Fin (angularPartitionCount ℓ))
    {b : Plane → UnitCircle → ℝ} (hb : Measurable (uncurry b))
    (hbound : ∀ x w, |b x w| ≤ 1) (x x' : Plane) (r : ℝ) :
    ‖∫ w, orthogonalityCircleKernel K ℓ arc b x x' r w ∂circleArcLength‖ ≤ 2 * ℓ :=
  (norm_integral_le_integral_norm _).trans
    (integral_norm_orthogonalityCircleKernel_le K hℓ hℓ₁ arc hb hbound x x' r)

theorem integral_orthogonalityCircleKernel_eq_angular (K : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (arc : Fin (angularPartitionCount ℓ)) {b : Plane → UnitCircle → ℝ}
    (hb : Measurable (uncurry b)) (x x' : Plane) (r : ℝ) :
    (∫ w, orthogonalityCircleKernel K ℓ arc b x x' r w ∂circleArcLength) =
      ∫ t in (equalAngularCellCenter (angularPartitionCount ℓ) arc - Real.pi)..
        (equalAngularCellCenter (angularPartitionCount ℓ) arc + Real.pi),
        Complex.exp ((orthogonalityAngularPhase r (x - x') t : ℂ) * Complex.I) *
          orthogonalityAngularAmplitude K ℓ arc b x x' t := by
  rw [integral_circle_eq_interval
    ((measurable_orthogonalityCircleKernel K hℓ arc hb x x').of_uncurry_left)
      (equalAngularCellCenter (angularPartitionCount ℓ) arc - Real.pi),
    show equalAngularCellCenter (angularPartitionCount ℓ) arc - Real.pi + 2 * Real.pi =
      equalAngularCellCenter (angularPartitionCount ℓ) arc + Real.pi by ring]
  simp_rw [orthogonalityCircleKernel_comp_angle]

end FalconerThetaGauge
