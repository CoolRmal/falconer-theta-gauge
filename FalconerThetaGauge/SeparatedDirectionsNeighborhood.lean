module

public import FalconerThetaGauge.SeparatedDirectionsArc
public import FalconerThetaGauge.DirectionalTestsWideningGeometry

/-! # Actual angular neighborhoods and their geometric chord bounds -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function

namespace FalconerThetaGauge

theorem self_subset_closedArcNeighborhood (δ : ℝ) (Z : Set UnitCircle) :
    Z ⊆ closedArcNeighborhood δ Z := by
  intro w hw
  refine ⟨circleAngle w, Metric.self_subset_cthickening _ ?_, unitCircleOfAngle_circleAngle w⟩
  change unitCircleOfAngle (circleAngle w) ∈ Z
  simpa only [unitCircleOfAngle_circleAngle] using hw

theorem angularPassingSet_closedArcNeighborhood (δ : ℝ) (Z : Set UnitCircle) :
    angularPassingSet (closedArcNeighborhood δ Z) =
      Metric.cthickening δ (angularPassingSet Z) := by
  ext θ
  change unitCircleOfAngle θ ∈ closedArcNeighborhood δ Z ↔ _
  rw [mem_closedArcNeighborhood_iff, circleAngle_unitCircleOfAngle]
  have hp : Periodic (fun θ : ℝ ↦ θ ∈ Metric.cthickening δ (angularPassingSet Z))
      (2 * Real.pi) := by
    intro t
    exact propext (cthickening_periodic_set (angularPassingSet_periodic Z) t)
  exact of_eq (periodic_apply_toIocMod hp θ)

theorem closedArcNeighborhood_closedArcNeighborhood_subset {δ ε : ℝ}
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (Z : Set UnitCircle) :
    closedArcNeighborhood δ (closedArcNeighborhood ε Z) ⊆
      closedArcNeighborhood (δ + ε) Z := by
  rintro w ⟨θ, hθ, rfl⟩
  rw [angularPassingSet_closedArcNeighborhood] at hθ
  exact ⟨θ, Metric.cthickening_cthickening_subset hδ hε _ hθ, rfl⟩

/-- A genuine angular closed neighborhood increases a uniform chord-radius bound
by at most its literal angular radius, including its boundary. -/
theorem norm_sub_le_of_mem_closedArcNeighborhood {δ r : ℝ} (hδ : 0 ≤ δ)
    {Z : Set UnitCircle} {c w : UnitCircle}
    (hZ : ∀ z ∈ Z, ‖(z : Plane) - (c : Plane)‖ ≤ r)
    (hw : w ∈ closedArcNeighborhood δ Z) :
    ‖(w : Plane) - (c : Plane)‖ ≤ δ + r := by
  apply le_of_forall_gt
  intro b hb
  obtain ⟨z, hz, hwz⟩ := exists_mem_norm_sub_lt_of_closedArcNeighborhood hδ
    (show δ < b - r by linarith) hw
  have htri := dist_triangle (w : Plane) (z : Plane) (c : Plane)
  simp only [dist_eq_norm] at htri
  have hzbound := hZ z hz
  linarith

theorem norm_sub_le_of_mem_closedDirectionArc (α : ℝ) {r : ℝ}
    {w : UnitCircle} (hw : w ∈ closedDirectionArc α r) :
    ‖(w : Plane) - (unitCircleOfAngle α : Plane)‖ ≤ r := by
  obtain ⟨θ, hθ, rfl⟩ := hw
  exact (norm_angularDirection_sub_le θ α).trans (abs_le.mpr (by
    constructor <;> linarith [hθ.1, hθ.2]))

theorem norm_sub_le_of_mem_antipodal_closedDirectionArc (α : ℝ) {r : ℝ}
    {w : UnitCircle} (hw : w ∈ circleAntipode '' closedDirectionArc α r) :
    ‖(w : Plane) - (circleAntipode (unitCircleOfAngle α) : Plane)‖ ≤ r := by
  obtain ⟨z, hz, rfl⟩ := hw
  rw [coe_circleAntipode, coe_circleAntipode,
    show -(z : Plane) - -(unitCircleOfAngle α : Plane) =
      -((z : Plane) - (unitCircleOfAngle α : Plane)) by abel, norm_neg]
  exact norm_sub_le_of_mem_closedDirectionArc α hz

/-- The source `0.2` support neighborhood and the `π/3` neighborhood of the
oppositely oriented arc are genuinely disjoint subsets of the actual circle. -/
theorem prepared_arc_neighborhood_disjoint_opposite (α : ℝ) :
    Disjoint (closedArcNeighborhood (1 / 5) (closedDirectionArc α (1 / 40)))
      (closedArcNeighborhood (Real.pi / 3)
        (circleAntipode '' closedDirectionArc α (1 / 40))) := by
  apply Set.disjoint_left.mpr
  intro w hw hwo
  have hnear := norm_sub_le_of_mem_closedArcNeighborhood (by norm_num : (0 : ℝ) ≤ 1 / 5)
    (fun z hz ↦ norm_sub_le_of_mem_closedDirectionArc α hz) hw
  have hopposite := norm_sub_le_of_mem_closedArcNeighborhood
    (by positivity : 0 ≤ Real.pi / 3)
    (fun z hz ↦ norm_sub_le_of_mem_antipodal_closedDirectionArc α hz) hwo
  have hcenters : ‖(unitCircleOfAngle α : Plane) -
      (circleAntipode (unitCircleOfAngle α) : Plane)‖ = 2 := by
    rw [coe_circleAntipode, sub_neg_eq_add, ← two_smul ℝ,
      norm_smul, norm_coe_unitCircle]
    norm_num
  have htri := dist_triangle (unitCircleOfAngle α : Plane) (w : Plane)
    (circleAntipode (unitCircleOfAngle α) : Plane)
  simp only [dist_eq_norm] at htri
  rw [hcenters, norm_sub_rev (unitCircleOfAngle α : Plane) (w : Plane)] at htri
  linarith [Real.pi_lt_four]

end FalconerThetaGauge
