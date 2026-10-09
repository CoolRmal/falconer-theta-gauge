module

public import FalconerThetaGauge.DirectionalTestsWideningGeometry

/-! # Quantitative passing-test stability under the actual angular mask thickening -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical ContDiff

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- The exact dyadic motion budget behind the constant eight in Lemma 6.7. -/
theorem directional_widening_budget {a b : ℕ} (hab : a ≤ b) (E : ℝ)
    {width width' : ℝ} (hgap : 8 * (2 : ℝ) ^ (-E) ≤ width - width') :
    4 * (2 : ℝ) ^ (-(a : ℝ)) *
      (2 * ((2 : ℝ) ^ (-((b - a : ℕ) : ℝ)) * (2 : ℝ) ^ E)) ≤
      (width - width') * (2 : ℝ) ^ (-(b : ℝ)) * (2 : ℝ) ^ (2 * E) := by
  have hpow : (2 : ℝ) ^ (-(a : ℝ)) * (2 : ℝ) ^ (-((b - a : ℕ) : ℝ)) =
      (2 : ℝ) ^ (-(b : ℝ)) := by
    rw [← Real.rpow_add (by norm_num), Nat.cast_sub hab]
    congr 1
    ring
  have hE : (2 : ℝ) ^ (-E) * (2 : ℝ) ^ (2 * E) = (2 : ℝ) ^ E := by
    rw [← Real.rpow_add (by norm_num)]
    congr 1
    ring
  calc
    _ = 8 * (2 : ℝ) ^ (-(b : ℝ)) * (2 : ℝ) ^ E := by
      calc
        _ = 8 * ((2 : ℝ) ^ (-(a : ℝ)) * (2 : ℝ) ^ (-((b - a : ℕ) : ℝ))) *
            (2 : ℝ) ^ E := by ring
        _ = _ := by rw [hpow]
    _ = (8 * (2 : ℝ) ^ (-E)) * (2 : ℝ) ^ (-(b : ℝ)) * (2 : ℝ) ^ (2 * E) := by
      rw [show (8 * (2 : ℝ) ^ (-E)) * (2 : ℝ) ^ (-(b : ℝ)) *
          (2 : ℝ) ^ (2 * E) = 8 * (2 : ℝ) ^ (-(b : ℝ)) *
          ((2 : ℝ) ^ (-E) * (2 : ℝ) ^ (2 * E)) by ring, hE]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hgap (by positivity)) (by positivity)

/-- Literal tube inclusion under the exact source width gap and chord scale. -/
theorem directionalTube_subset_of_norm_sub_le {g p : ℕ} (hgp : g ≤ p) (E : ℝ)
    {width width' δ : ℝ} (hδ : δ ≤ (2 : ℝ) ^ (-((p - g : ℕ) : ℝ)) * (2 : ℝ) ^ E)
    (hgap : 8 * (2 : ℝ) ^ (-E) ≤ width - width') (c : Plane)
    {w w₀ : UnitCircle} (hw : ‖(w : Plane) - (w₀ : Plane)‖ ≤ 2 * δ) :
    directionalTube g p E width' c w ⊆ directionalTube g p E width c w₀ := by
  intro z hz
  obtain ⟨hline, hradius⟩ := hz
  refine ⟨?_, hradius⟩
  have hmove : ‖z - c‖ * ‖(w : Plane) - (w₀ : Plane)‖ ≤
      (width - width') * (2 : ℝ) ^ (-(p : ℝ)) * (2 : ℝ) ^ (2 * E) := by
    calc
      _ ≤ (4 * (2 : ℝ) ^ (-(g : ℝ))) * (2 * δ) :=
        mul_le_mul hradius hw (norm_nonneg _) (by positivity)
      _ ≤ 4 * (2 : ℝ) ^ (-(g : ℝ)) *
          (2 * ((2 : ℝ) ^ (-((p - g : ℕ) : ℝ)) * (2 : ℝ) ^ E)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hδ (by norm_num)) (by positivity)
      _ ≤ _ := directional_widening_budget hgp E hgap
  have h := (directionLineResidual_norm_le_add c z w w₀).trans (add_le_add hline hmove)
  convert h using 1
  ring

/-- Literal occupied-center counts obey the same genuine tube inclusion. -/
theorem tubeCount_le_of_norm_sub_le (ρ : Measure Plane) {g p : ℕ} (hgp : g ≤ p) (E : ℝ)
    {width width' δ : ℝ} (hδ : δ ≤ (2 : ℝ) ^ (-((p - g : ℕ) : ℝ)) * (2 : ℝ) ^ E)
    (hgap : 8 * (2 : ℝ) ^ (-E) ≤ width - width') (P : Fin 2 → ℤ)
    {w w₀ : UnitCircle} (hw : ‖(w : Plane) - (w₀ : Plane)‖ ≤ 2 * δ) :
    tubeCount ρ g p E width' P w ≤ tubeCount ρ g p E width P w₀ := by
  rw [tubeCount_eq_card, tubeCount_eq_card]
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro Q hQ
  obtain ⟨hQocc, hQdir⟩ := Finset.mem_filter.mp hQ
  exact Finset.mem_filter.mpr ⟨hQocc,
    directionalTube_subset_of_norm_sub_le hgp E hδ hgap _ hw hQdir⟩

/-- The half-open dyadic anchor's pair diameter has the needed strict factor two. -/
theorem norm_sub_lt_two_dyadicRadius {p : ℕ} {P : Fin 2 → ℤ} {z z' : Plane}
    (hz : z ∈ dyadicCube p P) (hz' : z' ∈ dyadicCube p P) :
    ‖z - z'‖ < 2 * (2 : ℝ) ^ (-(p : ℝ)) := by
  have h₁ := dyadicCube_subset_ball_center p P hz
  have h₂ := dyadicCube_subset_ball_center p P hz'
  have h := lt_of_le_of_lt (dist_triangle z (dyadicCubeCenter p P) z')
    (add_lt_add (Metric.mem_ball.mp h₁) (by simpa only [dist_comm] using Metric.mem_ball.mp h₂))
  simpa only [dist_eq_norm, dyadicRadius, two_mul] using h

/-- The normalized anchor restriction is genuinely carried by that anchor. -/
theorem ae_mem_projectionAnchorMeasure (ρ : Measure Plane) (p : ℕ) (P : Fin 2 → ℤ) :
    ∀ᵐ z ∂projectionAnchorMeasure ρ p P, z ∈ dyadicCube p P := by
  unfold projectionAnchorMeasure normalizedRestrict
  exact Measure.ae_smul_measure (ae_restrict_mem (measurableSet_dyadicCube p P)) _

/-- Actual pair-coincidence inclusion on the genuine anchor square. -/
theorem projectionCoincidenceSet_on_anchor_subset_of_norm_sub_le {p u : ℕ} (hpu : p ≤ u)
    (E : ℝ) {width width' δ : ℝ}
    (hδ : δ ≤ (2 : ℝ) ^ (-((u - p : ℕ) : ℝ)) * (2 : ℝ) ^ E)
    (hgap : 8 * (2 : ℝ) ^ (-E) ≤ width - width') (P : Fin 2 → ℤ)
    {w w₀ : UnitCircle} (hw : ‖(w : Plane) - (w₀ : Plane)‖ ≤ 2 * δ) :
    projectionCoincidenceSet u E width' w ∩ (dyadicCube p P ×ˢ dyadicCube p P) ⊆
      projectionCoincidenceSet u E width w₀ := by
  rintro ⟨z, z'⟩ ⟨hz, hzP, hz'P⟩
  have hradius : ‖z - z'‖ ≤ 4 * (2 : ℝ) ^ (-(p : ℝ)) := by
    have h := norm_sub_lt_two_dyadicRadius hzP hz'P
    have hp : 0 < (2 : ℝ) ^ (-(p : ℝ)) := by positivity
    linarith
  have hmove : ‖z - z'‖ * ‖(w : Plane) - (w₀ : Plane)‖ ≤
      (width - width') * (2 : ℝ) ^ (-(u : ℝ)) * (2 : ℝ) ^ (2 * E) := by
    calc
      _ ≤ (4 * (2 : ℝ) ^ (-(p : ℝ))) * (2 * δ) :=
        mul_le_mul hradius hw (norm_nonneg _) (by positivity)
      _ ≤ 4 * (2 : ℝ) ^ (-(p : ℝ)) *
          (2 * ((2 : ℝ) ^ (-((u - p : ℕ) : ℝ)) * (2 : ℝ) ^ E)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hδ (by norm_num)) (by positivity)
      _ ≤ _ := directional_widening_budget hpu E hgap
  have h := (abs_inner_direction_le_add z z' w w₀).trans (add_le_add hz hmove)
  change |inner ℝ (z - z') (w₀ : Plane)| ≤ _
  convert h using 1
  ring

/-- The literal normalized projection counts inherit the actual anchor inclusion. -/
theorem projectionCount_le_of_norm_sub_le (ρ : Measure Plane) [IsFiniteMeasure ρ]
    {p u : ℕ} (hpu : p ≤ u) (E : ℝ) {width width' δ : ℝ}
    (hδ : δ ≤ (2 : ℝ) ^ (-((u - p : ℕ) : ℝ)) * (2 : ℝ) ^ E)
    (hgap : 8 * (2 : ℝ) ^ (-E) ≤ width - width') (P : Fin 2 → ℤ)
    (hP : 0 < unitCellWeight ρ p P) {w w₀ : UnitCircle}
    (hw : ‖(w : Plane) - (w₀ : Plane)‖ ≤ 2 * δ) :
    projectionCount ρ p u E width' P w ≤ projectionCount ρ p u E width P w₀ := by
  have := isProbabilityMeasure_projectionAnchorMeasure ρ p P hP
  have hcarried : ∀ᵐ zz ∂(projectionAnchorMeasure ρ p P).prod
      (projectionAnchorMeasure ρ p P), zz ∈ dyadicCube p P ×ˢ dyadicCube p P := by
    apply Measure.ae_prod_mem_iff_ae_ae_mem
      ((measurableSet_dyadicCube p P).prod (measurableSet_dyadicCube p P)) |>.mpr
    filter_upwards [ae_mem_projectionAnchorMeasure ρ p P] with z hz
    filter_upwards [ae_mem_projectionAnchorMeasure ρ p P] with z' hz'
    exact ⟨hz, hz'⟩
  unfold projectionCount projectionCountOfMeasure Measure.real
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hcarried] with zz hzz
  intro hz
  exact projectionCoincidenceSet_on_anchor_subset_of_norm_sub_le hpu E hδ hgap P hw ⟨hz, hzz⟩

/-- Literal scheduled counts are stable throughout the full untruncated test scale. -/
theorem scheduledDirectionalCount_le_of_norm_sub_scale (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (E : ℝ) {width width' : ℝ} (hgap : 8 * (2 : ℝ) ^ (-E) ≤ width - width')
    (test : ProfileScheduleTest)
    (htube : test.kind = .tube → test.endpoint ≤ test.anchor)
    (hprojection : test.kind = .projection → test.anchor ≤ test.endpoint)
    (P : Fin 2 → ℤ) (hP : 0 < unitCellWeight ρ test.anchor P)
    {w w₀ : UnitCircle}
    (hw : ‖(w : Plane) - (w₀ : Plane)‖ ≤
      2 * ((2 : ℝ) ^ (-(test.length : ℝ)) * (2 : ℝ) ^ E)) :
    scheduledDirectionalCount ρ E width' test P w ≤
      scheduledDirectionalCount ρ E width test P w₀ := by
  cases h : test.kind
  · simp only [scheduledDirectionalCount, h]
    apply tubeCount_le_of_norm_sub_le ρ (htube h) E _ hgap P hw
    simp only [ProfileScheduleTest.length, h]
    exact le_rfl
  · simp only [scheduledDirectionalCount, h]
    apply projectionCount_le_of_norm_sub_le ρ (hprojection h) E _ hgap P hP hw
    simp only [ProfileScheduleTest.length, h]
    exact le_rfl

/-- Literal scheduled counts are stable under the source's truncated mask scale. -/
theorem scheduledDirectionalCount_le_of_norm_sub_le (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (E : ℝ) {width width' : ℝ} (hgap : 8 * (2 : ℝ) ^ (-E) ≤ width - width')
    (test : ProfileScheduleTest)
    (htube : test.kind = .tube → test.endpoint ≤ test.anchor)
    (hprojection : test.kind = .projection → test.anchor ≤ test.endpoint)
    (P : Fin 2 → ℤ) (hP : 0 < unitCellWeight ρ test.anchor P)
    {w w₀ : UnitCircle}
    (hw : ‖(w : Plane) - (w₀ : Plane)‖ ≤ 2 * scheduledMaskScale E test) :
    scheduledDirectionalCount ρ E width' test P w ≤
      scheduledDirectionalCount ρ E width test P w₀ :=
  scheduledDirectionalCount_le_of_norm_sub_scale ρ E hgap test htube hprojection P hP
    (hw.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)))

/-- Lemma 6.7's widened closed arc neighborhood genuinely passes the smaller width. -/
theorem closedArcNeighborhood_scheduledPassing_subset (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (E : ℝ) {width width' : ℝ} (hgap : 8 * (2 : ℝ) ^ (-E) ≤ width - width')
    (test : ProfileScheduleTest)
    (htube : test.kind = .tube → test.endpoint ≤ test.anchor)
    (hprojection : test.kind = .projection → test.anchor ≤ test.endpoint)
    (P : Fin 2 → ℤ) (hP : 0 < unitCellWeight ρ test.anchor P) :
    closedArcNeighborhood (2 * scheduledMaskScale E test)
      (scheduledPassingDirections ρ E width test P) ⊆
        scheduledPassingDirections ρ E width' test P := by
  intro w hw
  obtain ⟨w₀, hw₀, hww₀⟩ :=
    exists_mem_norm_sub_lt_radius_of_closedArcNeighborhood
      (mul_pos (by norm_num) (scheduledMaskScale_pos E test)) hw
  exact (scheduledDirectionalCount_le_of_norm_sub_le ρ E hgap test htube hprojection P hP
    hww₀.le).trans hw₀

end FalconerThetaGauge
