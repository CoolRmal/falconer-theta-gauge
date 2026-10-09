module

public import FalconerThetaGauge.DistanceLinearizationMassShortened
public import FalconerThetaGauge.DistanceLinearizationGroups

/-! # Exact finite regrouping of the actual retained cell distance measures -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

def finiteScalarGroupIndices {ι : Type*} [Fintype ι] (index : ι → ℤ) : Finset ℤ :=
  Finset.univ.image index

abbrev finiteScalarGroupFiber {ι : Type*} [Fintype ι] (index : ι → ℤ)
    (g : finiteScalarGroupIndices index) := {i : ι // index i = (g : ℤ)}

def finiteScalarGroupMeasure {ι : Type*} [Fintype ι] (η : ι → Measure ℝ)
    (index : ι → ℤ)
    (g : finiteScalarGroupIndices index) : Measure ℝ :=
  Measure.sum fun i : finiteScalarGroupFiber index g ↦ η i.1

instance {ι : Type*} [Fintype ι] (η : ι → Measure ℝ) [∀ i, IsFiniteMeasure (η i)]
    (index : ι → ℤ) (g : finiteScalarGroupIndices index) :
    IsFiniteMeasure (finiteScalarGroupMeasure η index g) := by
  unfold finiteScalarGroupMeasure
  infer_instance

theorem sum_finiteScalarGroupMeasures {ι : Type*} [Fintype ι]
    (η : ι → Measure ℝ) (index : ι → ℤ) :
    Measure.sum (finiteScalarGroupMeasure η index) = Measure.sum η := by
  let e : (Σ g : finiteScalarGroupIndices index, finiteScalarGroupFiber index g) ≃ ι :=
    { toFun := fun z ↦ z.2.1
      invFun := fun i ↦
        ⟨⟨index i, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩, ⟨i, rfl⟩⟩
      left_inv := by rintro ⟨⟨g, hg⟩, ⟨i, hi⟩⟩; dsimp at hi; subst g; rfl
      right_inv := fun _ ↦ rfl }
  ext s hs
  simp only [finiteScalarGroupMeasure, Measure.sum_apply _ hs, tsum_fintype]
  calc
    _ = ∑ z : (Σ g : finiteScalarGroupIndices index, finiteScalarGroupFiber index g),
        η z.2.1 s :=
      (Fintype.sum_sigma (fun z :
        (Σ g : finiteScalarGroupIndices index, finiteScalarGroupFiber index g) ↦
          η z.2.1 s)).symm
    _ = _ := e.sum_comp (fun i ↦ η i s)

/-- Actual cell pairs supply the true interval carriers for their scalar distance measures. -/
theorem ae_crossDistanceMeasure_cell_group (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (p : ℕ) (P Q : Fin 2 → ℤ) :
    ∀ᵐ s ∂crossDistanceMeasure (ρ.restrict (dyadicCube p P)) (ρ.restrict (dyadicCube p Q)),
      s ∈ linearizationDistanceGroupInterval p (linearizationDistanceGroupIndex p P Q) := by
  rw [crossDistanceMeasure, ae_map_iff continuous_dist.measurable.aemeasurable]
  · filter_upwards [ae_restricted_product_carriers ρ ρ
      (measurableSet_dyadicCube p P) (measurableSet_dyadicCube p Q)] with z hz
    exact pair_distance_mem_group_interval hz.1 hz.2
  · exact measurableSet_Ico

theorem ae_finiteScalarGroupMeasure_interval {ι : Type*} [Fintype ι]
    (η : ι → Measure ℝ) (index : ι → ℤ) (p : ℕ)
    (hη : ∀ i, ∀ᵐ s ∂η i, s ∈ linearizationDistanceGroupInterval p (index i))
    (g : finiteScalarGroupIndices index) :
    ∀ᵐ s ∂finiteScalarGroupMeasure η index g,
      s ∈ linearizationDistanceGroupInterval p (g : ℤ) := by
  rw [finiteScalarGroupMeasure, Measure.ae_sum_iff]
  intro i
  simpa only [i.2] using hη i.1

end FalconerThetaGauge
