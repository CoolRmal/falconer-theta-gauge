module

public import FalconerThetaGauge.DirectionalTestsRecords
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # The actual angular and affine-line motion estimates for widening tests -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman

/-- The exact chord length of the genuine Euclidean angle parametrization. -/
theorem norm_angularDirection_sub_eq (a b : ℝ) :
    ‖angularDirection a - angularDirection b‖ = ‖2 * Real.sin ((a - b) / 2)‖ := by
  have he : Complex.I * (a : ℂ) = Complex.I * ((a - b : ℝ) : ℂ) +
      Complex.I * (b : ℂ) := by push_cast; ring
  have hf : Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ)) =
      (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) *
        Complex.exp (Complex.I * (b : ℂ)) := by
    rw [he, Complex.exp_add]
    ring
  rw [angularDirection, angularDirection, ← LinearIsometryEquiv.map_sub,
    LinearIsometryEquiv.norm_map]
  have hcos (t : ℝ) : (Real.cos t : ℂ) + Real.sin t * Complex.I =
      Complex.exp (Complex.I * (t : ℂ)) := by
    rw [mul_comm Complex.I, Complex.exp_mul_I]
    simp only [Complex.ofReal_cos, Complex.ofReal_sin]
  rw [hcos, hcos, hf, norm_mul]
  simpa only [Complex.norm_exp_I_mul_ofReal, mul_one] using
    Complex.norm_exp_I_mul_ofReal_sub_one (a - b)

/-- Chords are bounded by their angular lift distance, including across branch cuts. -/
theorem norm_angularDirection_sub_le (a b : ℝ) :
    ‖angularDirection a - angularDirection b‖ ≤ |a - b| := by
  rw [norm_angularDirection_sub_eq, Real.norm_eq_abs, abs_mul, Nat.abs_ofNat]
  calc
    _ ≤ 2 * |(a - b) / 2| := mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = |a - b| := by rw [abs_div, Nat.abs_ofNat]; ring

theorem norm_angularDirection_sub_lt {a b : ℝ} (hab : a ≠ b) :
    ‖angularDirection a - angularDirection b‖ < |a - b| := by
  rw [norm_angularDirection_sub_eq, Real.norm_eq_abs, abs_mul, Nat.abs_ofNat]
  calc
    _ < 2 * |(a - b) / 2| := mul_lt_mul_of_pos_left
      (Real.abs_sin_lt_abs (div_ne_zero (sub_ne_zero.mpr hab) (by norm_num))) (by norm_num)
    _ = |a - b| := by rw [abs_div, Nat.abs_ofNat]; ring

/-- Every point of a closed arc neighborhood has genuine passing directions
arbitrarily close beyond the stated radius. No closedness of the passing set is assumed. -/
theorem exists_mem_norm_sub_lt_of_closedArcNeighborhood {δ r : ℝ} (hδ : 0 ≤ δ)
    (hr : δ < r) {Z : Set UnitCircle} {w : UnitCircle}
    (hw : w ∈ closedArcNeighborhood δ Z) :
    ∃ w₀ ∈ Z, ‖(w : Plane) - (w₀ : Plane)‖ < r := by
  obtain ⟨a, ha, rfl⟩ := hw
  have ht : a ∈ Metric.thickening r (angularPassingSet Z) :=
    Metric.cthickening_subset_thickening (δ₁ := ⟨δ, hδ⟩) hr _ ha
  obtain ⟨b, hb, hab⟩ := Metric.mem_thickening_iff.mp ht
  refine ⟨unitCircleOfAngle b, hb, ?_⟩
  exact (norm_angularDirection_sub_le a b).trans_lt (by simpa only [Real.dist_eq] using hab)

/-- Strict chord shortening also holds at the boundary of a closed arc
neighborhood, even when the passing set is merely Borel or completely arbitrary. -/
theorem exists_mem_norm_sub_lt_radius_of_closedArcNeighborhood {δ : ℝ} (hδ : 0 < δ)
    {Z : Set UnitCircle} {w : UnitCircle} (hw : w ∈ closedArcNeighborhood δ Z) :
    ∃ w₀ ∈ Z, ‖(w : Plane) - (w₀ : Plane)‖ < δ := by
  obtain ⟨a, ha, rfl⟩ := hw
  rw [Metric.cthickening_eq_biUnion_closedBall _ hδ.le] at ha
  obtain ⟨b, hb, hab⟩ := mem_iUnion₂.mp ha
  have hnorm : ‖angularDirection a - angularDirection b‖ < δ := by
    by_cases heq : a = b
    · simp only [heq, sub_self, norm_zero]
      exact hδ
    · exact (norm_angularDirection_sub_lt heq).trans_le
        (by simpa only [Metric.mem_closedBall, Real.dist_eq] using hab)
  have hopen : IsOpen {t : ℝ | ‖angularDirection a - angularDirection t‖ < δ} :=
    isOpen_lt (continuous_const.sub continuous_angularDirection).norm continuous_const
  obtain ⟨t, ht, htZ⟩ := mem_closure_iff.mp hb _ hopen hnorm
  exact ⟨unitCircleOfAngle t, htZ, ht⟩

/-- Rotating the true affine line changes its distance by at most the point's
radius times the chord length. This uses the closest point on the original line. -/
theorem directionLineResidual_norm_le_add (c z : Plane) (w w₀ : UnitCircle) :
    ‖directionLineResidual c w₀ z‖ ≤ ‖directionLineResidual c w z‖ +
      ‖z - c‖ * ‖(w : Plane) - (w₀ : Plane)‖ := by
  have hw : ‖(w : Plane)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using w.property
  have ht : |inner ℝ (w : Plane) (z - c)| ≤ ‖z - c‖ := by
    simpa only [Real.norm_eq_abs, hw, one_mul] using
      norm_inner_le_norm (𝕜 := ℝ) (w : Plane) (z - c)
  calc
    _ ≤ ‖z - c - inner ℝ (w : Plane) (z - c) • (w₀ : Plane)‖ :=
      directionLineResidual_norm_le c z w₀ _
    _ = ‖directionLineResidual c w z +
        inner ℝ (w : Plane) (z - c) • ((w : Plane) - (w₀ : Plane))‖ := by
      congr 1
      simp only [directionLineResidual, smul_sub]
      module
    _ ≤ ‖directionLineResidual c w z‖ +
        ‖inner ℝ (w : Plane) (z - c) • ((w : Plane) - (w₀ : Plane))‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right ht (norm_nonneg _))

/-- The true dot product changes by at most the pair distance times the chord. -/
theorem abs_inner_direction_le_add (z z' : Plane) (w w₀ : UnitCircle) :
    |inner ℝ (z - z') (w₀ : Plane)| ≤ |inner ℝ (z - z') (w : Plane)| +
      ‖z - z'‖ * ‖(w : Plane) - (w₀ : Plane)‖ := by
  calc
    _ = |inner ℝ (z - z') (w : Plane) -
        inner ℝ (z - z') ((w : Plane) - (w₀ : Plane))| := by rw [inner_sub_right]; ring_nf
    _ ≤ |inner ℝ (z - z') (w : Plane)| +
        |inner ℝ (z - z') ((w : Plane) - (w₀ : Plane))| := abs_sub _ _
    _ ≤ _ := by
      apply add_le_add le_rfl
      simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (z - z')
        ((w : Plane) - (w₀ : Plane))

end FalconerThetaGauge
