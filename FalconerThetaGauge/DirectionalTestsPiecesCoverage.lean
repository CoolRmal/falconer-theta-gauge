/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.DirectionalTestsPiecesPartition
public import FalconerThetaGauge.RegularMeasureEntryPieceLists
public import FalconerThetaGauge.FilteredDistanceMeasureRegularCarriers

/-! # Literal regular-piece carriers lie in occupied cells at every listed anchor -/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem regularMeasureEntryDepth_le_scale (ρ : Measure Plane) (θ : ℝ) (N : ℕ) :
    regularMeasureEntryDepth ρ θ N ≤ N := by
  unfold regularMeasureEntryDepth profileEntryDepth
  apply Finset.sup_le
  intro n hn
  have hnr := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
  change n ≤ N
  omega

theorem regularMeasurePieceTests_anchor_le_scale (ρ : Measure Plane) {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) {test : ProfileScheduleTest}
    (htest : test ∈ regularMeasurePieceTests ρ θ N) : test.anchor ≤ N := by
  have hq : 0 < blockCount θ N := blockCount_pos θ (by have := hpar.1; omega)
  rcases Finset.mem_union.mp htest with hentry | hscheduled
  · have heq : test = ⟨.tube, regularMeasureEntryDepth ρ θ N, 0⟩ :=
      Finset.mem_singleton.mp hentry
    subst test
    exact regularMeasureEntryDepth_le_scale ρ θ N
  · obtain ⟨a, t, _, ht, _, _, _, _, _, hlength, _⟩ :=
      profileScheduledTests_origin hq (le_refl N) hscheduled
    omega

/-- Every point of the original retained carrier lies in a positive-mass cell of its
normalized restriction at every depth at most `N`. -/
theorem regularDyadicPartCarrier_subset_occupiedCells (μ : Measure Plane) [IsFiniteMeasure μ]
    (ε κ : ℝ) {N n : ℕ} (hn : n ≤ N) {t : List ℕ}
    (ht : t ∈ regularDyadicKeptTypes μ ε κ N) :
    regularDyadicPartCarrier μ ε N t ⊆
      cellUnion n (occupiedUnitCells (regularDyadicPartMeasure μ ε N t) n) := by
  intro x hx
  obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
  have hxa := mem_dyadicCube_ancestor_of_mem hn hxk
  have hkH := regularDyadicPartLeaves_subset μ ε N t hk
  have hkU := regularDyadicHeavyCells_subset μ N hkH
  have hxU := dyadicCube_subset_unitSquare N hkU hxk
  have hpU : ancestor (N - n) k ∈ unitCellIndices n := by
    rw [← mem_dyadicCube_iff.mp hxa]
    exact cubeIndex_mem_unitCellIndices n hxU
  have hweight : 0 < unitCellWeight μ N k := regularDyadicHeavyCells_positive μ N k hkH
  have hkfilter : k ∈ (regularDyadicPartLeaves μ ε N t).filter
      (fun j => ancestor (N - n) j = ancestor (N - n) k) :=
    Finset.mem_filter.mpr ⟨hk, rfl⟩
  have hsum : 0 < ∑ j ∈ (regularDyadicPartLeaves μ ε N t).filter
      (fun j => ancestor (N - n) j = ancestor (N - n) k), unitCellWeight μ N j :=
    hweight.trans_le (Finset.single_le_sum (fun j _ => unitCellWeight_nonneg μ N j) hkfilter)
  have hmass : 0 < unitCellWeight (regularDyadicPartMeasure μ ε N t) n
      (ancestor (N - n) k) := by
    change 0 < (normalizedRestrict μ (cellUnion N (regularDyadicPartLeaves μ ε N t))).real
      (dyadicCube n (ancestor (N - n) k))
    rw [real_normalizedRestrict_cellUnion_dyadicCube μ hn]
    exact mul_pos (inv_pos.mpr (regularDyadicPartCarrier_mass_pos μ ε κ N ht)) hsum
  exact mem_iUnion₂.mpr ⟨ancestor (N - n) k,
    Finset.mem_filter.mpr ⟨hpU, hmass⟩, hxa⟩

/-- The concrete normalized piece, actual entry list, occupied anchor tests and smooth masks. -/
def regularPieceDirectionalFilter (μ : Measure Plane) [IsProbabilityMeasure μ]
    {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) (K : ℕ)
    (t : {t // t ∈ regularDyadicKeptTypes μ (tolerance θ N) (blockParameter θ N) N}) :
    FiniteDirectionalFilter N (tolerance θ N * N) := by
  let ρ := regularDyadicPartMeasure μ (tolerance θ N) N t.val
  letI : IsProbabilityMeasure ρ :=
    (regularDyadicPartMeasure_probability μ (tolerance θ N) (blockParameter θ N) N t.property).1
  exact scheduledDirectionalFilter ρ N (tolerance θ N * N) K
    (regularMeasurePieceTests ρ θ N)
    (profilePieceTests_card_le_scale_sq_add_one (regularMeasureExcess ρ N) hpar)
    (regularDyadicPartCarrier μ (tolerance θ N) N t.val)
    (measurableSet_regularDyadicPartCarrier μ (tolerance θ N) N t.val)
    (fun test htest => regularDyadicPartCarrier_subset_occupiedCells μ
      (tolerance θ N) (blockParameter θ N)
      (regularMeasurePieceTests_anchor_le_scale ρ hpar htest) t.property)

theorem regularPieceDirectionalFilter_carrier (μ : Measure Plane) [IsProbabilityMeasure μ]
    {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) (K : ℕ)
    (t : {t // t ∈ regularDyadicKeptTypes μ (tolerance θ N) (blockParameter θ N) N}) :
    (regularPieceDirectionalFilter μ hpar K t).carrier =
      regularDyadicPartCarrier μ (tolerance θ N) N t.val := rfl

end FalconerThetaGauge
