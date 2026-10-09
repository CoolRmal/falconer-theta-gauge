module

public import FalconerThetaGauge.ExplicitBumpPeriodic
public import FalconerThetaGauge.ExplicitBumpDerivativeBudget
public import FalconerThetaGauge.FilteredDistanceMeasureCircle

/-! # Genuine circle masks with their globally smooth periodic angular pullback -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff

namespace FalconerThetaGauge

theorem norm_coe_unitCircle (w : UnitCircle) : ‖(w : Plane)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using w.property

/-- The principal angle of a genuine unit-circle point. -/
def circleAngle (w : UnitCircle) : ℝ := radialAngle 0 w

@[fun_prop]
theorem measurable_circleAngle : Measurable circleAngle := by
  change Measurable (fun w : UnitCircle ↦ radialAngle 0 (w : Plane))
  have hpair : Measurable (fun w : UnitCircle ↦ ((0 : Plane), (w : Plane))) :=
    measurable_const.prodMk measurable_subtype_coe
  have h := measurable_radialAngle.comp hpair
  simpa only [Function.comp_def, Function.uncurry_apply_pair] using h

theorem unitCircleOfAngle_circleAngle (w : UnitCircle) : unitCircleOfAngle (circleAngle w) = w := by
  apply Subtype.ext
  have hw : (0 : Plane) ≠ (w : Plane) := by
    intro h
    have hn := norm_coe_unitCircle w
    rw [← h, norm_zero] at hn
    norm_num at hn
  simp only [coe_unitCircleOfAngle, circleAngle, angularDirection_radialAngle hw,
    sub_zero, norm_coe_unitCircle, inv_one, one_smul]

theorem circleAngle_unitCircleOfAngle (θ : ℝ) :
    circleAngle (unitCircleOfAngle θ) = toIocMod Real.two_pi_pos (-Real.pi) θ := by
  unfold circleAngle radialAngle
  simp only [coe_unitCircleOfAngle, sub_zero, angularDirection,
    LinearIsometryEquiv.symm_apply_apply]
  simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using
    Complex.arg_cos_add_sin_mul_I_eq_toIocMod θ

theorem periodic_apply_toIocMod {β : Type*} {f : ℝ → β}
    (hf : Periodic f (2 * Real.pi)) (θ : ℝ) :
    f (toIocMod Real.two_pi_pos (-Real.pi) θ) = f θ := by
  have h := toIocMod_add_toIocDiv_zsmul Real.two_pi_pos (-Real.pi) θ
  rw [zsmul_eq_mul] at h
  rw [eq_sub_iff_add_eq.mpr h]
  exact hf.sub_int_mul_eq _

theorem unitCircleOfAngle_add_two_pi (θ : ℝ) :
    unitCircleOfAngle (θ + 2 * Real.pi) = unitCircleOfAngle θ := by
  apply Subtype.ext
  simp [angularDirection, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem unitCircleOfAngle_add_pi (θ : ℝ) :
    unitCircleOfAngle (θ + Real.pi) = circleAntipode (unitCircleOfAngle θ) := by
  apply Subtype.ext
  simp only [coe_unitCircleOfAngle, coe_circleAntipode, angularDirection,
    Real.cos_add_pi, Real.sin_add_pi, Complex.ofReal_neg, neg_mul, ← neg_add,
    map_neg]

/-- Lift a Borel passing set on the circle to its actual periodic angular preimage. -/
def angularPassingSet (Z : Set UnitCircle) : Set ℝ := unitCircleOfAngle ⁻¹' Z

theorem angularPassingSet_periodic (Z : Set UnitCircle) (θ : ℝ) :
    θ + 2 * Real.pi ∈ angularPassingSet Z ↔ θ ∈ angularPassingSet Z := by
  simp only [angularPassingSet, mem_preimage, unitCircleOfAngle_add_two_pi]

/-- A true symbol on the circle, obtained by descending the actual convolution mask. -/
def circlePassingMask (K : ℕ) (δ : ℝ) (Z : Set UnitCircle) (w : UnitCircle) : ℝ :=
  explicitPassingMask K δ (angularPassingSet Z) (circleAngle w)

theorem circlePassingMask_comp_angle (K : ℕ) (δ : ℝ) (Z : Set UnitCircle) (θ : ℝ) :
    circlePassingMask K δ Z (unitCircleOfAngle θ) =
      explicitPassingMask K δ (angularPassingSet Z) θ := by
  rw [circlePassingMask, circleAngle_unitCircleOfAngle]
  exact periodic_apply_toIocMod
    (explicitPassingMask_periodic K δ (angularPassingSet_periodic Z)) θ

@[fun_prop]
theorem measurable_circlePassingMask (K : ℕ) {δ : ℝ} (hδ : 0 < δ) (Z : Set UnitCircle) :
    Measurable (circlePassingMask K δ Z) :=
  (contDiff_explicitPassingMask K hδ _).continuous.measurable.comp measurable_circleAngle

theorem circlePassingMask_mem_Icc (K : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (Z : Set UnitCircle) (w : UnitCircle) : circlePassingMask K δ Z w ∈ Icc 0 1 :=
  explicitPassingMask_mem_Icc K hδ _ _

theorem circlePassingMask_eq_one (K : ℕ) {δ : ℝ} (hδ : 0 < δ) {Z : Set UnitCircle}
    {w : UnitCircle} (hw : w ∈ Z) : circlePassingMask K δ Z w = 1 := by
  apply explicitPassingMask_eq_one K hδ
  change unitCircleOfAngle (circleAngle w) ∈ Z
  simpa only [unitCircleOfAngle_circleAngle] using hw

/-- The closed arc neighborhood is defined by actual angle lifts, with no branch-cut artifact. -/
def closedArcNeighborhood (δ : ℝ) (Z : Set UnitCircle) : Set UnitCircle :=
  unitCircleOfAngle '' Metric.cthickening δ (angularPassingSet Z)

theorem mem_closedArcNeighborhood_iff (δ : ℝ) (Z : Set UnitCircle) (w : UnitCircle) :
    w ∈ closedArcNeighborhood δ Z ↔
      circleAngle w ∈ Metric.cthickening δ (angularPassingSet Z) := by
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    rw [circleAngle_unitCircleOfAngle]
    have hp : Periodic (fun θ : ℝ ↦ θ ∈ Metric.cthickening δ (angularPassingSet Z))
        (2 * Real.pi) := by
      intro θ
      exact propext (cthickening_periodic_set (angularPassingSet_periodic Z) θ)
    have h := periodic_apply_toIocMod hp θ
    rw [h]
    exact hθ
  · intro h
    exact ⟨circleAngle w, h, unitCircleOfAngle_circleAngle w⟩

theorem measurableSet_closedArcNeighborhood (δ : ℝ) (Z : Set UnitCircle) :
    MeasurableSet (closedArcNeighborhood δ Z) := by
  have heq : closedArcNeighborhood δ Z =
      circleAngle ⁻¹' Metric.cthickening δ (angularPassingSet Z) := by
    ext w
    exact mem_closedArcNeighborhood_iff δ Z w
  rw [heq]
  exact measurable_circleAngle Metric.isClosed_cthickening.measurableSet

theorem circlePassingMask_eq_zero (K : ℕ) {δ : ℝ} (hδ : 0 < δ) (Z : Set UnitCircle)
    {w : UnitCircle} (hw : w ∉ closedArcNeighborhood (2 * δ) Z) :
    circlePassingMask K δ Z w = 0 := by
  apply explicitPassingMask_eq_zero K hδ
  intro h
  exact hw ⟨circleAngle w, h, unitCircleOfAngle_circleAngle w⟩

theorem contDiff_circlePassingMask_comp_angle (K : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (Z : Set UnitCircle) :
    ContDiff ℝ ∞ (fun θ ↦ circlePassingMask K δ Z (unitCircleOfAngle θ)) := by
  have heq : (fun θ ↦ circlePassingMask K δ Z (unitCircleOfAngle θ)) =
      explicitPassingMask K δ (angularPassingSet Z) := funext (circlePassingMask_comp_angle K δ Z)
  rw [heq]
  exact contDiff_explicitPassingMask K hδ _

theorem norm_iteratedDeriv_circlePassingMask_comp_angle_le {T : ℕ} (hT : 2 ≤ T)
    {k : ℕ} (hk : k ≤ 6 * T) {δ : ℝ} (hδ : 0 < δ) (Z : Set UnitCircle) (θ : ℝ) :
    ‖iteratedDeriv k (fun θ ↦ circlePassingMask (6 * T) δ Z (unitCircleOfAngle θ)) θ‖ ≤
      ((4 * (T : ℝ)) ^ 3 / δ) ^ k := by
  have heq : (fun θ ↦ circlePassingMask (6 * T) δ Z (unitCircleOfAngle θ)) =
      explicitPassingMask (6 * T) δ (angularPassingSet Z) :=
    funext (circlePassingMask_comp_angle (6 * T) δ Z)
  rw [heq]
  exact norm_iteratedDeriv_explicitPassingMask_le_polynomial_base hT hk hδ _ θ

theorem angularPassingSet_antipodal (Z : Set UnitCircle)
    (hZ : ∀ w, circleAntipode w ∈ Z ↔ w ∈ Z) (θ : ℝ) :
    θ + Real.pi ∈ angularPassingSet Z ↔ θ ∈ angularPassingSet Z := by
  simp only [angularPassingSet, mem_preimage, unitCircleOfAngle_add_pi, hZ]

theorem circlePassingMask_antipodal (K : ℕ) (δ : ℝ) (Z : Set UnitCircle)
    (hZ : ∀ w, circleAntipode w ∈ Z ↔ w ∈ Z) (w : UnitCircle) :
    circlePassingMask K δ Z (circleAntipode w) = circlePassingMask K δ Z w := by
  conv_lhs => rw [← unitCircleOfAngle_circleAngle w]
  rw [← unitCircleOfAngle_add_pi, circlePassingMask_comp_angle]
  exact explicitPassingMask_periodic K δ (angularPassingSet_antipodal Z hZ) (circleAngle w)

end FalconerThetaGauge
