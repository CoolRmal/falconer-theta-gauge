module

public import FalconerThetaGauge.RegularDecompositionDyadicTypes

/-!
# Regular probability measures from the actual retained cell types

Depths in the source range from zero to the terminal generation `N`. Regularity
is expressed by pairwise comparison of actual cell masses on that range, which
is equivalent to comparison with the largest occupied cell.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset
open scoped Classical ENNReal

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- The occupied cell masses are comparable at every depth of the finite construction. -/
def IsRegularThrough (ε : ℝ) (N : ℕ) (ρ : Measure Plane) : Prop :=
  ∀ n ≤ N, ∀ p q : Fin 2 → ℤ, 0 < ρ.real (dyadicCube n q) →
    ρ.real (dyadicCube n p) ≤ (2 : ℝ) ^ (ε * N) * ρ.real (dyadicCube n q)

/-- The original terminal leaves of one complete bottom-up type. -/
def regularDyadicPartLeaves (μ : Measure Plane) (ε : ℝ) (N : ℕ) (t : List ℕ) :
    Finset (Fin 2 → ℤ) :=
  (regularDyadicHeavyCells μ N).filter (fun k ↦ regularDyadicType μ ε N k = t)

/-- The actual Borel carrier of one type, a finite union of original terminal cells. -/
def regularDyadicPartCarrier (μ : Measure Plane) (ε : ℝ) (N : ℕ) (t : List ℕ) : Set Plane :=
  cellUnion N (regularDyadicPartLeaves μ ε N t)

/-- The literal normalized restriction to that carrier. -/
def regularDyadicPartMeasure (μ : Measure Plane) (ε : ℝ) (N : ℕ) (t : List ℕ) : Measure Plane :=
  normalizedRestrict μ (regularDyadicPartCarrier μ ε N t)

theorem measurableSet_regularDyadicPartCarrier (μ : Measure Plane) (ε : ℝ)
    (N : ℕ) (t : List ℕ) : MeasurableSet (regularDyadicPartCarrier μ ε N t) :=
  measurableSet_cellUnion N _

theorem regularDyadicPartLeaves_subset (μ : Measure Plane) (ε : ℝ) (N : ℕ) (t : List ℕ) :
    regularDyadicPartLeaves μ ε N t ⊆ regularDyadicHeavyCells μ N := Finset.filter_subset _ _

theorem regularDyadicPartCarrier_disjoint (μ : Measure Plane) (ε : ℝ) (N : ℕ)
    {s t : List ℕ} (hst : s ≠ t) :
    Disjoint (regularDyadicPartCarrier μ ε N s) (regularDyadicPartCarrier μ ε N t) := by
  apply cellUnion_disjoint
  apply Finset.disjoint_left.mpr
  intro k hks hkt
  exact hst ((Finset.mem_filter.mp hks).2.symm.trans (Finset.mem_filter.mp hkt).2)

theorem real_regularDyadicPartCarrier (μ : Measure Plane) [IsFiniteMeasure μ]
    (ε : ℝ) (N : ℕ) (t : List ℕ) :
    μ.real (regularDyadicPartCarrier μ ε N t) =
      finiteTypeMass (regularDyadicHeavyCells μ N) (unitCellWeight μ N)
        (regularDyadicType μ ε N) t := by
  exact real_cellUnion μ N _

/-- Normalization multiplies every original cell mass by the same positive factor. -/
theorem real_normalizedRestrict_cellUnion_dyadicCube (μ : Measure Plane)
    [IsFiniteMeasure μ] {n N : ℕ} (hn : n ≤ N) (S : Finset (Fin 2 → ℤ)) (p : Fin 2 → ℤ) :
    (normalizedRestrict μ (cellUnion N S)).real (dyadicCube n p) =
      (μ.real (cellUnion N S))⁻¹ *
        ∑ k ∈ S.filter (fun k ↦ ancestor (N - n) k = p), unitCellWeight μ N k := by
  rw [normalizedRestrict, measureReal_ennreal_smul_apply,
    real_restrict_cellUnion_dyadicCube μ hn, ENNReal.toReal_inv]
  rfl

/-- An occupied coarser cell contains an original positive-weight leaf of its type. -/
theorem exists_regularDyadicPart_leaf_of_cell_mass_pos (μ : Measure Plane)
    [IsProbabilityMeasure μ] (ε : ℝ) {n N : ℕ} (hn : n ≤ N) (t : List ℕ)
    (p : Fin 2 → ℤ)
    (hp : 0 < (regularDyadicPartMeasure μ ε N t).real (dyadicCube n p)) :
    ∃ k ∈ regularDyadicPartLeaves μ ε N t, ancestor (N - n) k = p := by
  by_contra! h
  have hempty : (regularDyadicPartLeaves μ ε N t).filter
      (fun k ↦ ancestor (N - n) k = p) = ∅ := by
    ext k
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
    exact h k
  change 0 < (normalizedRestrict μ (cellUnion N (regularDyadicPartLeaves μ ε N t))).real
    (dyadicCube n p) at hp
  rw [real_normalizedRestrict_cellUnion_dyadicCube μ hn, hempty,
    Finset.sum_empty, mul_zero] at hp
  exact lt_irrefl 0 hp

/-- For a leaf of the chosen type, its actual coarser fiber is exactly the
intermediate family used in the original-weight combinatorial proof. -/
theorem regularDyadicPartLeaves_filter_eq_generation (μ : Measure Plane) (ε : ℝ)
    (N m : ℕ) (t : List ℕ) {k : Fin 2 → ℤ}
    (hk : k ∈ regularDyadicPartLeaves μ ε N t) :
    (regularDyadicPartLeaves μ ε N t).filter (fun j ↦ ancestor m j = ancestor m k) =
      regularDyadicGenerationFamily μ ε N m k := by
  have hkt := (Finset.mem_filter.mp hk).2
  ext j
  simp only [regularDyadicPartLeaves, regularDyadicGenerationFamily,
    regularIntermediateFamily, Finset.mem_filter]
  change ((j ∈ regularDyadicHeavyCells μ N ∧ regularDyadicType μ ε N j = t) ∧
    ancestor m j = ancestor m k) ↔
      j ∈ regularDyadicHeavyCells μ N ∧ ancestor m j = ancestor m k ∧
        regularDyadicType μ ε N j = regularDyadicType μ ε N k
  rw [hkt]
  tauto

/-- Every actual normalized type is regular throughout the stated finite range. -/
theorem regularDyadicPartMeasure_isRegularThrough (μ : Measure Plane)
    [IsProbabilityMeasure μ] {ε : ℝ} {N : ℕ} (hεN : 16 ≤ ε * N) (t : List ℕ) :
    IsRegularThrough ε N (regularDyadicPartMeasure μ ε N t) := by
  intro n hn p q hq
  by_cases hp : 0 < (regularDyadicPartMeasure μ ε N t).real (dyadicCube n p)
  · obtain ⟨x, hx, hxp⟩ := exists_regularDyadicPart_leaf_of_cell_mass_pos μ ε hn t p hp
    obtain ⟨y, hy, hyq⟩ := exists_regularDyadicPart_leaf_of_cell_mass_pos μ ε hn t q hq
    have htype : regularDyadicType μ ε N x = regularDyadicType μ ε N y :=
      (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    have hcomp := (regularDyadicGeneration_mass_comparable μ hεN (Nat.sub_le N n)
      (regularDyadicPartLeaves_subset μ ε N t hx)
      (regularDyadicPartLeaves_subset μ ε N t hy) htype).le
    have hxgen := regularDyadicPartLeaves_filter_eq_generation μ ε N (N - n) t hx
    have hygen := regularDyadicPartLeaves_filter_eq_generation μ ε N (N - n) t hy
    rw [hxp] at hxgen
    rw [hyq] at hygen
    change (normalizedRestrict μ (cellUnion N (regularDyadicPartLeaves μ ε N t))).real
      (dyadicCube n p) ≤ (2 : ℝ) ^ (ε * N) *
        (normalizedRestrict μ (cellUnion N (regularDyadicPartLeaves μ ε N t))).real
          (dyadicCube n q)
    rw [real_normalizedRestrict_cellUnion_dyadicCube μ hn,
      real_normalizedRestrict_cellUnion_dyadicCube μ hn, hxgen, hygen]
    calc
      _ ≤ (μ.real (cellUnion N (regularDyadicPartLeaves μ ε N t)))⁻¹ *
          ((2 : ℝ) ^ (ε * N) *
            ∑ z ∈ regularDyadicGenerationFamily μ ε N (N - n) y,
              unitCellWeight μ N z) :=
        mul_le_mul_of_nonneg_left hcomp (inv_nonneg.mpr measureReal_nonneg)
      _ = _ := by ring
  · have hpzero : (regularDyadicPartMeasure μ ε N t).real (dyadicCube n p) = 0 :=
      le_antisymm (le_of_not_gt hp) measureReal_nonneg
    rw [hpzero]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) measureReal_nonneg

/-- The indices of the actual parts surviving the whole-type discard. -/
def regularDyadicKeptTypes (μ : Measure Plane) (ε κ : ℝ) (N : ℕ) : Finset (List ℕ) :=
  (regularDyadicRetainedCells μ ε κ N).image (regularDyadicType μ ε N)

theorem regularDyadicRetainedCells_subset_heavy (μ : Measure Plane) (ε κ : ℝ) (N : ℕ) :
    regularDyadicRetainedCells μ ε κ N ⊆ regularDyadicHeavyCells μ N :=
  Finset.filter_subset _ _

/-- Every kept part has the exact original mass threshold required in Lemma 5.8. -/
theorem regularDyadicPartCarrier_mass_ge (μ : Measure Plane) [IsFiniteMeasure μ]
    (ε κ : ℝ) (N : ℕ) {t : List ℕ} (ht : t ∈ regularDyadicKeptTypes μ ε κ N) :
    (2 : ℝ) ^ (-(κ * N / 2)) ≤ μ.real (regularDyadicPartCarrier μ ε N t) := by
  obtain ⟨k, hk, hkt⟩ := Finset.mem_image.mp ht
  rw [real_regularDyadicPartCarrier, ← hkt]
  exact (Finset.mem_filter.mp hk).2

theorem regularDyadicPartCarrier_mass_pos (μ : Measure Plane) [IsFiniteMeasure μ]
    (ε κ : ℝ) (N : ℕ) {t : List ℕ} (ht : t ∈ regularDyadicKeptTypes μ ε κ N) :
    0 < μ.real (regularDyadicPartCarrier μ ε N t) :=
  (Real.rpow_pos_of_pos (by norm_num) _).trans_le
    (regularDyadicPartCarrier_mass_ge μ ε κ N ht)

/-- A surviving part is an actual probability carried by the half-open unit square. -/
theorem regularDyadicPartMeasure_probability (μ : Measure Plane) [IsProbabilityMeasure μ]
    (ε κ : ℝ) (N : ℕ) {t : List ℕ} (ht : t ∈ regularDyadicKeptTypes μ ε κ N) :
    IsProbabilityMeasure (regularDyadicPartMeasure μ ε N t) ∧
      regularDyadicPartMeasure μ ε N t unitSquare = 1 := by
  have hpos : μ (regularDyadicPartCarrier μ ε N t) ≠ 0 := by
    have hp := regularDyadicPartCarrier_mass_pos μ ε κ N ht
    intro hzero
    simp only [Measure.real, hzero, ENNReal.toReal_zero, lt_self_iff_false] at hp
  have hfin := measure_ne_top μ (regularDyadicPartCarrier μ ε N t)
  refine ⟨isProbabilityMeasure_normalizedRestrict hpos hfin, ?_⟩
  change ((μ (cellUnion N (regularDyadicPartLeaves μ ε N t)))⁻¹ •
    μ.restrict (cellUnion N (regularDyadicPartLeaves μ ε N t))) unitSquare = 1
  rw [Measure.smul_apply, smul_eq_mul,
    restrict_cellUnion_unitSquare μ N _
      ((regularDyadicPartLeaves_subset μ ε N t).trans (regularDyadicHeavyCells_subset μ N))]
  exact ENNReal.inv_mul_cancel hpos hfin

/-- Whole-type retention keeps all original terminal leaves of each surviving type. -/
theorem regularDyadicPartLeaves_subset_retained (μ : Measure Plane) (ε κ : ℝ) (N : ℕ)
    {t : List ℕ} (ht : t ∈ regularDyadicKeptTypes μ ε κ N) :
    regularDyadicPartLeaves μ ε N t ⊆ regularDyadicRetainedCells μ ε κ N := by
  obtain ⟨k, hk, hkt⟩ := Finset.mem_image.mp ht
  obtain ⟨hkH, hkmass⟩ := Finset.mem_filter.mp hk
  intro j hj
  obtain ⟨hjH, hjt⟩ := Finset.mem_filter.mp hj
  apply Finset.mem_filter.mpr
  refine ⟨hjH, ?_⟩
  rw [hjt, ← hkt]
  exact hkmass

/-- The surviving planar carriers have exactly the surviving terminal leaves. -/
theorem biUnion_regularDyadicPartCarrier (μ : Measure Plane) (ε κ : ℝ) (N : ℕ) :
    (⋃ t ∈ regularDyadicKeptTypes μ ε κ N, regularDyadicPartCarrier μ ε N t) =
      cellUnion N (regularDyadicRetainedCells μ ε κ N) := by
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hxt
    exact mem_iUnion₂.mpr
      ⟨k, regularDyadicPartLeaves_subset_retained μ ε κ N ht hk, hxk⟩
  · intro hx
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
    refine mem_iUnion₂.mpr ⟨regularDyadicType μ ε N k,
      Finset.mem_image.mpr ⟨k, hk, rfl⟩, ?_⟩
    exact mem_iUnion₂.mpr ⟨k, Finset.mem_filter.mpr
      ⟨regularDyadicRetainedCells_subset_heavy μ ε κ N hk, rfl⟩, hxk⟩

/-- The measure discarded from the actual planar source satisfies the literal budget. -/
theorem regularDyadicPartCarrier_discarded_mass_le (μ : Measure Plane)
    [IsProbabilityMeasure μ] {ε κ : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (hκ : κ ≤ 4)
    {N : ℕ} (hεN : 16 ≤ ε * N)
    (hbudget : Real.log (49 / ε) / Real.log 2 + (333 / 100 : ℝ) * (8 / ε + 1) ≤ κ * N / 4) :
    μ.real (unitSquare \
      ⋃ t ∈ regularDyadicKeptTypes μ ε κ N, regularDyadicPartCarrier μ ε N t) ≤
        2 * (2 : ℝ) ^ (-(κ * N / 4)) := by
  rw [biUnion_regularDyadicPartCarrier, real_unitSquare_diff_cellUnion]
  exact regularDyadicType_discarded_mass_le μ hε hε₁ hκ hεN hbudget

/-- The actual retained type count also satisfies the literal (P2) budget. -/
theorem regularDyadicKeptTypes_card_le (μ : Measure Plane) [IsProbabilityMeasure μ]
    {ε κ : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) {N : ℕ} (hεN : 16 ≤ ε * N)
    (hbudget : Real.log (49 / ε) / Real.log 2 + (333 / 100 : ℝ) * (8 / ε + 1) ≤ κ * N / 4) :
    ((regularDyadicKeptTypes μ ε κ N).card : ℝ) ≤ (2 : ℝ) ^ (κ * N / 4) := by
  apply le_trans _ (regularDyadicType_count_le μ hε hε₁ hεN hbudget)
  exact_mod_cast Finset.card_le_card
    (Finset.image_subset_image (regularDyadicRetainedCells_subset_heavy μ ε κ N))

/-- Lemma 5.8: disjoint original terminal-cell carriers with the stated retained
mass, discarded mass, number of types, and regular normalized probabilities. -/
theorem regular_decomposition (μ : Measure Plane) [IsProbabilityMeasure μ]
    {ε κ : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (hκ : κ ≤ 4) {N : ℕ}
    (hεN : 16 ≤ ε * N)
    (hbudget : Real.log (49 / ε) / Real.log 2 + (333 / 100 : ℝ) * (8 / ε + 1) ≤ κ * N / 4) :
    ∃ (T : Finset (List ℕ)) (G : List ℕ → Set Plane),
      (∀ t ∈ T, ∃ S : Finset (Fin 2 → ℤ), S ⊆ unitCellIndices N ∧
        (∀ k ∈ S, 0 < μ.real (dyadicCube N k)) ∧ G t = cellUnion N S) ∧
      (∀ s ∈ T, ∀ t ∈ T, s ≠ t → Disjoint (G s) (G t)) ∧
      (∀ t ∈ T, (2 : ℝ) ^ (-(κ * N / 2)) ≤ μ.real (G t)) ∧
      μ.real (unitSquare \ ⋃ t ∈ T, G t) ≤ 2 * (2 : ℝ) ^ (-(κ * N / 4)) ∧
      (∀ t ∈ T, IsProbabilityMeasure (normalizedRestrict μ (G t)) ∧
        normalizedRestrict μ (G t) unitSquare = 1 ∧
          IsRegularThrough ε N (normalizedRestrict μ (G t))) ∧
      (T.card : ℝ) ≤ (2 : ℝ) ^ (κ * N / 4) := by
  refine ⟨regularDyadicKeptTypes μ ε κ N, regularDyadicPartCarrier μ ε N,
    ?_, ?_, ?_, regularDyadicPartCarrier_discarded_mass_le μ hε hε₁ hκ hεN hbudget,
    ?_, regularDyadicKeptTypes_card_le μ hε hε₁ hεN hbudget⟩
  · intro t _
    refine ⟨regularDyadicPartLeaves μ ε N t,
      (regularDyadicPartLeaves_subset μ ε N t).trans (regularDyadicHeavyCells_subset μ N),
      ?_, rfl⟩
    intro k hk
    exact regularDyadicHeavyCells_positive μ N k (regularDyadicPartLeaves_subset μ ε N t hk)
  · intro s _ t _ hst
    exact regularDyadicPartCarrier_disjoint μ ε N hst
  · intro t ht
    exact regularDyadicPartCarrier_mass_ge μ ε κ N ht
  · intro t ht
    have hprob := regularDyadicPartMeasure_probability μ ε κ N ht
    exact ⟨hprob.1, hprob.2, regularDyadicPartMeasure_isRegularThrough μ hεN t⟩

end FalconerThetaGauge
