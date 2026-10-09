module

public import FalconerThetaGauge.DistanceLinearizationMassGroupBound

/-! # Source Estimate 7.7 for the actual unweighted passing distance measures -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem crossDistanceMeasure_cells_univ (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (p : ℕ) (P Q : Fin 2 → ℤ) :
    crossDistanceMeasure (ρ.restrict (dyadicCube p P)) (ρ.restrict (dyadicCube p Q)) univ =
      ρ (dyadicCube p P) * ρ (dyadicCube p Q) := by
  rw [crossDistanceMeasure, Measure.map_apply continuous_dist.measurable MeasurableSet.univ,
    preimage_univ, ← univ_prod_univ, Measure.prod_prod]
  simp

/-- Each actual retained pair supplies the true projection-test witness needed by the mass bound. -/
theorem retained_cell_collision_le_height (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {θ : ℝ} {N a p t : ℕ} (hpar : ParameterFacts θ N)
    (hreg : IsRegularThrough (tolerance θ N) N ρ) (hap : a ≤ p) {A B : Fin 2 → ℤ}
    (hsep : SeparatedDyadicCells a A B) (hpt : p < t) (ht : t ≤ N)
    (hdepth : a + t < 2 * p) {width width' : ℝ} (hwidth' : 1 ≤ width')
    (hgap : 8 * (2 : ℝ) ^ (-(tolerance θ N * N)) ≤ width - width')
    (I₁ I₂ : Finset ProfileScheduleTest) (hprojection : (⟨.projection, p, t⟩) ∈ I₂)
    (R : retainedFineCellPairs ρ a p A B
      (scheduledPassingPairSet ρ ρ (tolerance θ N * N) width I₁ I₂)) :
    scalarCollisionMass
        (crossDistanceMeasure (ρ.restrict (dyadicCube p R.1.1))
          (ρ.restrict (dyadicCube p R.1.2)))
        (crossDistanceMeasure (ρ.restrict (dyadicCube p R.1.1))
          (ρ.restrict (dyadicCube p R.1.2))) (dyadicRadius t) 0 ≤
      ENNReal.ofReal (4 * linearizationCellCoefficient ρ θ N p t) *
        (crossDistanceMeasure (ρ.restrict (dyadicCube p R.1.1))
          (ρ.restrict (dyadicCube p R.1.2))) univ ^ (2 : ℕ) := by
  obtain ⟨hPQ, hwitness⟩ := Finset.mem_filter.1 R.2
  obtain ⟨hP, hQ⟩ := Finset.mem_product.1 hPQ
  obtain ⟨⟨x₀, y₀⟩, ⟨hx₀, hy₀⟩, hw₀⟩ := hwitness
  have hQmass := (Finset.mem_filter.1 hQ).2.2
  have hQocc : R.1.2 ∈ occupiedUnitCells ρ p :=
    Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hQ).1, hQmass⟩
  have hpass := ((mem_scheduledPassingPairSet_iff _ _ _ _ _ _ _).1 hw₀).2
    (⟨.projection, p, t⟩) hprojection
  have hpassQ : pairDirection x₀ y₀ ∈
      projectionPassingDirections ρ p t (tolerance θ N * N) width R.1.2 :=
    (mem_scheduledPassingPinSet_on_cell ρ _ width (⟨.projection, p, t⟩) hQocc hy₀ _).1 hpass
  have h := scalarCollisionMass_crossDistance_cells_le_height ρ hρ hpar hreg hsep
    (dyadicCube_subset_of_mem_occupiedCellDescendants ρ hap hP)
    (dyadicCube_subset_of_mem_occupiedCellDescendants ρ hap hQ) hpt.le ht hdepth
    hwidth' hgap hQmass hx₀ hy₀ hpassQ
  rw [crossDistanceMeasure_cells_univ, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  simpa only [dyadicRadius, mul_pow, mul_assoc, ENNReal.ofReal_ofNat] using h

/-- Genuine grouping and literal one-cell estimates give the full raw passing recurrence. -/
theorem passingUnweightedCollision_toReal_le_shortened (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {θ : ℝ} {N a p t : ℕ}
    (hpar : ParameterFacts θ N) (hreg : IsRegularThrough (tolerance θ N) N ρ)
    (hap : a ≤ p) {A B : Fin 2 → ℤ} (hsep : SeparatedDyadicCells a A B)
    (hpt : p < t) (ht : t ≤ N) (hdepth : a + t < 2 * p)
    {width width' : ℝ} (hwidth' : 1 ≤ width')
    (hgap : 8 * (2 : ℝ) ^ (-(tolerance θ N * N)) ≤ width - width')
    {I₁ I₂ J₁ J₂ : Finset ProfileScheduleTest}
    (hprojection : (⟨.projection, p, t⟩) ∈ I₂)
    (hJ₁ : J₁ ⊆ I₁) (hJ₂ : J₂ ⊆ I₂)
    (hordered₁ : ScheduledTestsOrdered J₁) (hordered₂ : ScheduledTestsOrdered J₂)
    (hshort₁ : ∀ test ∈ J₁, test.anchor ≤ p ∧ a + test.length ≤ p)
    (hshort₂ : ∀ test ∈ J₂, test.anchor ≤ p ∧ a + test.length ≤ p) :
    (scalarCollisionMass
        (passingUnweightedDistanceMeasure ρ ρ (dyadicCube a A) (dyadicCube a B)
          (scheduledPassingPairSet ρ ρ (tolerance θ N * N) width I₁ I₂))
        (passingUnweightedDistanceMeasure ρ ρ (dyadicCube a A) (dyadicCube a B)
          (scheduledPassingPairSet ρ ρ (tolerance θ N * N) width I₁ I₂))
        (dyadicRadius t) 0).toReal ≤
      972 * linearizationCellCoefficient ρ θ N p t *
        (scalarCollisionMass
          (passingUnweightedDistanceMeasure ρ ρ (dyadicCube a A) (dyadicCube a B)
            (scheduledPassingPairSet ρ ρ (tolerance θ N * N) width' J₁ J₂))
          (passingUnweightedDistanceMeasure ρ ρ (dyadicCube a A) (dyadicCube a B)
            (scheduledPassingPairSet ρ ρ (tolerance θ N * N) width' J₁ J₂))
          (dyadicRadius p) 0).toReal := by
  let I := retainedFineCellPairs ρ a p A B
    (scheduledPassingPairSet ρ ρ (tolerance θ N * N) width I₁ I₂)
  let η : I → Measure ℝ := fun R ↦ crossDistanceMeasure
    (ρ.restrict (dyadicCube p R.1.1)) (ρ.restrict (dyadicCube p R.1.2))
  let : ∀ R, IsFiniteMeasure (η R) := fun R ↦ by
    dsimp [η, crossDistanceMeasure]
    infer_instance
  have hfirst : passingUnweightedDistanceMeasure ρ ρ (dyadicCube a A) (dyadicCube a B)
      (scheduledPassingPairSet ρ ρ (tolerance θ N * N) width I₁ I₂) ≤ Measure.sum η := by
    rw [← passingUnweightedDistanceMeasure_retained_eq_sum ρ hap]
    exact passingUnweightedDistanceMeasure_le_retained ρ hρ hap _ _ _
  have hN : 0 < N := by have := hpar.1; omega
  have hlast : Measure.sum η ≤ passingUnweightedDistanceMeasure ρ ρ
      (dyadicCube a A) (dyadicCube a B)
      (scheduledPassingPairSet ρ ρ (tolerance θ N * N) width' J₁ J₂) :=
    sum_crossDistanceMeasure_retained_le_shortened ρ hap hsep
      (mul_nonneg (tolerance_pos θ hN).le (Nat.cast_nonneg N)) hgap hJ₁ hJ₂
      hordered₁ hordered₂ hshort₁ hshort₂
  have hgroup := scalarCollisionMass_sum_toReal_le_group_bound η hpt
    (fun R ↦ linearizationDistanceGroupIndex p R.1.1 R.1.2)
    (fun R ↦ ae_crossDistanceMeasure_cell_group ρ p R.1.1 R.1.2)
    (mul_nonneg (by norm_num) (linearizationCellCoefficient_pos ρ θ N p t).le)
    (fun R ↦ retained_cell_collision_le_height ρ hρ hpar hreg hap hsep hpt ht hdepth
      hwidth' hgap I₁ I₂ hprojection R)
  have hbefore := ENNReal.toReal_mono (by finiteness)
    (Measure.le_iff.1 (Measure.prod_mono hfirst hfirst) _
      (measurableSet_scalarCollision (dyadicRadius t) 0))
  have hafter := ENNReal.toReal_mono (by finiteness)
    (Measure.le_iff.1 (Measure.prod_mono hlast hlast) _
      (measurableSet_scalarCollision (dyadicRadius p) 0))
  simp only [scalarCollisionMass] at hgroup ⊢
  apply hbefore.trans
  apply hgroup.trans
  have hc : 0 ≤ 972 * linearizationCellCoefficient ρ θ N p t :=
    mul_nonneg (by norm_num : (0 : ℝ) ≤ 972)
      (linearizationCellCoefficient_pos ρ θ N p t).le
  convert mul_le_mul_of_nonneg_left hafter hc using 1
  ring

end FalconerThetaGauge
