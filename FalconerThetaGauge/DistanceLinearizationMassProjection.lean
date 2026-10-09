module

public import FalconerThetaGauge.DistanceLinearizationMass
public import FalconerThetaGauge.DirectionalTestsProjection

/-! # Exact normalization of the one-cell projection and distance masses -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal RealInnerProductSpace

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem smul_projectionAnchorMeasure_eq_restrict (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (p : ℕ) (Q : Fin 2 → ℤ) (hQ : 0 < unitCellWeight ρ p Q) :
    ρ (dyadicCube p Q) • projectionAnchorMeasure ρ p Q = ρ.restrict (dyadicCube p Q) := by
  have hmass : ρ (dyadicCube p Q) ≠ 0 := (ENNReal.toReal_pos_iff.1 hQ).1.ne'
  rw [projectionAnchorMeasure, normalizedRestrict, smul_smul,
    ENNReal.mul_inv_cancel hmass (measure_ne_top ρ _), one_smul]

/-- The unnormalized pair coincidence is exactly the literal normalized count times cell mass². -/
theorem projectionShiftedPairMass_restrict_eq_count (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (p t : ℕ) (E : ℝ) (Q : Fin 2 → ℤ) (hQ : 0 < unitCellWeight ρ p Q) (w : UnitCircle) :
    projectionShiftedPairMass (ρ.restrict (dyadicCube p Q)) w
        ((2 : ℝ) ^ (-(t : ℝ)) * (2 : ℝ) ^ (2 * E)) 0 =
      (ρ (dyadicCube p Q)) ^ (2 : ℕ) * ENNReal.ofReal (projectionCount ρ p t E 1 Q w) := by
  let ν := projectionAnchorMeasure ρ p Q
  let : IsProbabilityMeasure ν := isProbabilityMeasure_projectionAnchorMeasure ρ p Q hQ
  have hμ : ρ.restrict (dyadicCube p Q) = ρ (dyadicCube p Q) • ν :=
    (smul_projectionAnchorMeasure_eq_restrict ρ p Q hQ).symm
  rw [projectionShiftedPairMass, hμ, Measure.prod_smul_left, Measure.prod_smul_right,
    smul_smul, Measure.smul_apply, smul_eq_mul, pow_two]
  change _ = _ * ENNReal.ofReal ((ν.prod ν) (projectionCoincidenceSet t E 1 w)).toReal
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  congr 1
  congr 1
  ext z
  simp only [projectionCoincidenceSet, mem_ofPred_eq, sub_zero, one_mul, real_inner_comm]

/-- Source §7.7's one-cell-pair estimate, with the actual normalized projection count. -/
theorem scalarCollisionMass_crossDistance_cells_le_four_count (ρ : Measure Plane)
    [IsFiniteMeasure ρ] {a p t : ℕ} {A B P Q : Fin 2 → ℤ}
    (hsep : SeparatedDyadicCells a A B) (hP : dyadicCube p P ⊆ dyadicCube a A)
    (hQ : dyadicCube p Q ⊆ dyadicCube a B) (hdepth : a + t < 2 * p)
    (hQmass : 0 < unitCellWeight ρ p Q) {E : ℝ} (hE : 2 ≤ (2 : ℝ) ^ (2 * E)) :
    scalarCollisionMass
        (crossDistanceMeasure (ρ.restrict (dyadicCube p P)) (ρ.restrict (dyadicCube p Q)))
        (crossDistanceMeasure (ρ.restrict (dyadicCube p P)) (ρ.restrict (dyadicCube p Q)))
        ((2 : ℝ) ^ (-(t : ℝ))) 0 ≤
      4 * ENNReal.ofReal (projectionCount ρ p t E 1 Q
          (pairDirection (dyadicCellCenter p P) (dyadicCellCenter p Q))) *
        (ρ (dyadicCube p P)) ^ (2 : ℕ) * (ρ (dyadicCube p Q)) ^ (2 : ℕ) := by
  let w := pairDirection (dyadicCellCenter p P) (dyadicCellCenter p Q)
  let h := (2 : ℝ) ^ (-(t : ℝ)) * (2 : ℝ) ^ (2 * E)
  have htol : 2 * (2 : ℝ) ^ (-(t : ℝ)) ≤ h := by
    dsimp only [h]
    calc
      _ = (2 : ℝ) ^ (-(t : ℝ)) * 2 := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hE (by positivity)
  calc
    _ ≤ projectionFourPointCollisionMass (ρ.restrict (dyadicCube p P))
        (ρ.restrict (dyadicCube p Q)) w h :=
      scalarCollisionMass_crossDistance_cells_le_projection ρ hsep hP hQ hdepth htol
    _ ≤ 4 * ((ρ.restrict (dyadicCube p P)) univ) ^ (2 : ℕ) *
        projectionShiftedPairMass (ρ.restrict (dyadicCube p Q)) w h 0 :=
      projectionFourPointCollisionMass_le_four _ _ w (by dsimp [h]; positivity)
    _ = _ := by
      rw [Measure.restrict_apply MeasurableSet.univ, univ_inter,
        projectionShiftedPairMass_restrict_eq_count ρ p t E Q hQmass w]
      ring

end FalconerThetaGauge
