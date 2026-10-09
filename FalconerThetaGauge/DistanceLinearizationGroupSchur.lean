module

public import FalconerThetaGauge.DistanceLinearizationGroupMeasures
public import FalconerThetaGauge.FiniteGraphSchur

/-! # Actual scalar group collisions obey the finite neighboring-group bound -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Classical

namespace FalconerThetaGauge

theorem scalarCollisionMass_cross_le_of_bin_bounds (η ζ : Measure ℝ) [SFinite ζ]
    {h : ℝ} (hh : 0 < h) (C m n : ℝ≥0∞)
    (hη : scalarBinSquareMass η h ≤ C * m ^ (2 : ℕ))
    (hζ : scalarBinSquareMass ζ h ≤ C * n ^ (2 : ℕ)) :
    scalarCollisionMass η ζ h 0 ≤ 3 * C * m * n := by
  have hroot {x b : ℝ≥0∞} (hb : b ≤ C * x ^ (2 : ℕ)) :
      b ^ (1 / 2 : ℝ) ≤ C ^ (1 / 2 : ℝ) * x := by
    have h := ENNReal.rpow_le_rpow hb (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ← ENNReal.rpow_two, ← ENNReal.rpow_mul] at h
    norm_num at h
    exact h
  calc
    _ ≤ 3 * (scalarBinSquareMass η h ^ (1 / 2 : ℝ) *
        scalarBinSquareMass ζ h ^ (1 / 2 : ℝ)) :=
      scalarCollisionMass_cross_le_three_bins η ζ hh
    _ ≤ 3 * ((C ^ (1 / 2 : ℝ) * m) * (C ^ (1 / 2 : ℝ) * n)) :=
      mul_le_mul' le_rfl (mul_le_mul' (hroot hη) (hroot hζ))
    _ = _ := by
      rw [show (C ^ (1 / 2 : ℝ) * m) * (C ^ (1 / 2 : ℝ) * n) =
          (C ^ (1 / 2 : ℝ) * C ^ (1 / 2 : ℝ)) * m * n by ring,
        ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num
      ring

/-- The only sparsity hypothesis is vanishing of actual cross-collision masses
outside the finite symmetric neighboring graph. -/
theorem scalarCollisionMass_sum_le_graph {ι : Type*} [Fintype ι]
    (η : ι → Measure ℝ) [∀ i, SFinite (η i)] {h : ℝ} (hh : 0 < h)
    (linked : ι → ι → Prop) [DecidableRel linked]
    (hsym : ∀ ⦃i j⦄, linked i j → linked j i) {D C : ℝ} (hC : 0 ≤ C)
    (m : ι → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hdegree : ∀ i, (((Finset.univ : Finset ι).filter (linked i)).card : ℝ) ≤ D)
    (hbins : ∀ i, scalarBinSquareMass (η i) h ≤
      ENNReal.ofReal C * ENNReal.ofReal (m i) ^ (2 : ℕ))
    (hunlinked : ∀ i j, ¬linked i j → scalarCollisionMass (η i) (η j) h 0 = 0) :
    scalarCollisionMass (Measure.sum η) (Measure.sum η) h 0 ≤
      ENNReal.ofReal (3 * C * D * ∑ i, m i ^ (2 : ℕ)) := by
  have hterm (i j : ι) : scalarCollisionMass (η i) (η j) h 0 ≤
      ENNReal.ofReal (if linked i j then 3 * C * (m i * m j) else 0) := by
    by_cases hij : linked i j
    · simp only [hij, ite_true]
      have h := scalarCollisionMass_cross_le_of_bin_bounds (η i) (η j) hh
        (ENNReal.ofReal C) (ENNReal.ofReal (m i)) (ENNReal.ofReal (m j)) (hbins i) (hbins j)
      convert h using 1
      simp only [ENNReal.ofReal_mul (hm i),
        ENNReal.ofReal_mul (by positivity : 0 ≤ 3 * C)]
      norm_num
      ring
    · simp only [hij, ite_false, ENNReal.ofReal_zero, hunlinked i j hij, le_refl]
  rw [scalarCollisionMass_sum]
  calc
    _ ≤ ∑ i, ∑ j, ENNReal.ofReal (if linked i j then 3 * C * (m i * m j) else 0) :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hterm i j
    _ = ENNReal.ofReal (3 * C *
        (∑ i, ∑ j, if linked i j then m i * m j else 0)) := by
      have hnonneg (i j : ι) :
          0 ≤ (if linked i j then 3 * C * (m i * m j) else 0) := by
        split_ifs
        · exact mul_nonneg (mul_nonneg (by norm_num) hC) (mul_nonneg (hm i) (hm j))
        · exact le_rfl
      have hrow (i : ι) :
          (∑ j, ENNReal.ofReal (if linked i j then 3 * C * (m i * m j) else 0)) =
            ENNReal.ofReal (∑ j, if linked i j then 3 * C * (m i * m j) else 0) :=
        (ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ hnonneg i j)).symm
      simp_rw [hrow]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦
        Finset.sum_nonneg fun j _ ↦ hnonneg i j)]
      congr 1
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      have h := finite_graph_schur Finset.univ linked hsym m (fun i _ ↦ hdegree i)
      have h' := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 3 * C)
      convert h' using 1
      ring)

end FalconerThetaGauge
