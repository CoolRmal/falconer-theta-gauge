module

public import FalconerThetaGauge.SpaceSplittingSeparatedCarriers

/-! # Genuine almost-everywhere finite coverage of the far comparable spatial terms -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical ENNReal

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

def spaceSplittingRootFourMeasure (ρ : Measure Plane) (a : ℕ) (X Y : Fin 2 → ℤ) :
    Measure ((Plane × Plane) × (Plane × Plane)) :=
  ((ρ.restrict (dyadicCube a X)).prod (ρ.restrict (dyadicCube a X))).prod
    ((ρ.restrict (dyadicCube a Y)).prod (ρ.restrict (dyadicCube a Y)))

instance (ρ : Measure Plane) [IsFiniteMeasure ρ] (a : ℕ) (X Y : Fin 2 → ℤ) :
    IsFiniteMeasure (spaceSplittingRootFourMeasure ρ a X Y) := by
  unfold spaceSplittingRootFourMeasure
  infer_instance

def spaceSplittingFarComparableSet (p : ℕ) : Set ((Plane × Plane) × (Plane × Plane)) :=
  {z | 5 / 2 * dyadicRadius p < max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2) ∧
    max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2) ≤
      2 * min (dist z.1.1 z.1.2) (dist z.2.1 z.2.2)}

theorem measurableSet_spaceSplittingFarComparableSet (p : ℕ) :
    MeasurableSet (spaceSplittingFarComparableSet p) := by
  have hmax : Measurable (fun z : (Plane × Plane) × (Plane × Plane) ↦
      max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2)) := by fun_prop
  have hmin : Measurable (fun z : (Plane × Plane) × (Plane × Plane) ↦
      2 * min (dist z.1.1 z.1.2) (dist z.2.1 z.2.2)) := by fun_prop
  exact (measurableSet_lt measurable_const hmax).inter (measurableSet_le hmax hmin)

/-- Every actual far comparable four-point term belongs to a finite separated depth carrier. -/
theorem ae_spaceSplittingFarComparable_mem_depth_carrier (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) (a p : ℕ) (X Y : Fin 2 → ℤ) :
    ∀ᵐ z ∂spaceSplittingRootFourMeasure ρ a X Y,
      z ∈ spaceSplittingFarComparableSet p →
        z ∈ ⋃ n ∈ Finset.Ioo a (p + 12),
          spaceSplittingSeparatedCarrier ρ a n X ×ˢ spaceSplittingSeparatedCarrier ρ a n Y := by
  have hocc (A : Fin 2 → ℤ) : ∀ᵐ x ∂ρ.restrict (dyadicCube a A),
      ∀ n : ℕ, a ≤ n → x ∈ cellUnion n (occupiedCellDescendants ρ a n A) := by
    apply ae_all_iff.2
    intro n
    by_cases han : a ≤ n
    · filter_upwards [ae_mem_cellUnion_occupiedCellDescendants ρ hρ han A] with x hx
      exact fun _ ↦ hx
    · exact Filter.Eventually.of_forall fun _ h ↦ False.elim (han h)
  have hpair (A : Fin 2 → ℤ) :
      ∀ᵐ z ∂(ρ.restrict (dyadicCube a A)).prod (ρ.restrict (dyadicCube a A)),
        (z.1 ∈ dyadicCube a A ∧ z.2 ∈ dyadicCube a A) ∧
          (∀ n, a ≤ n → z.1 ∈ cellUnion n (occupiedCellDescendants ρ a n A)) ∧
          (∀ n, a ≤ n → z.2 ∈ cellUnion n (occupiedCellDescendants ρ a n A)) := by
    have hx := (Measure.quasiMeasurePreserving_fst
      (μ := ρ.restrict (dyadicCube a A)) (ν := ρ.restrict (dyadicCube a A))).ae (hocc A)
    have hy := (Measure.quasiMeasurePreserving_snd
      (μ := ρ.restrict (dyadicCube a A)) (ν := ρ.restrict (dyadicCube a A))).ae (hocc A)
    filter_upwards [hx, hy, ae_restricted_product_carriers ρ ρ
      (measurableSet_dyadicCube a A) (measurableSet_dyadicCube a A)] with z hx hy hz
    exact ⟨hz, hx, hy⟩
  have hx := (Measure.quasiMeasurePreserving_fst
    (μ := (ρ.restrict (dyadicCube a X)).prod (ρ.restrict (dyadicCube a X)))
    (ν := (ρ.restrict (dyadicCube a Y)).prod (ρ.restrict (dyadicCube a Y)))).ae (hpair X)
  have hy := (Measure.quasiMeasurePreserving_snd
    (μ := (ρ.restrict (dyadicCube a X)).prod (ρ.restrict (dyadicCube a X)))
    (ν := (ρ.restrict (dyadicCube a Y)).prod (ρ.restrict (dyadicCube a Y)))).ae (hpair Y)
  filter_upwards [hx, hy] with z hx hy
  intro hfar
  have hroot : max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2) ≤ 3 / 2 * dyadicRadius a := by
    apply max_le
    · simpa only [dist_eq_norm] using norm_sub_le_of_mem_same_dyadicCube hx.1.1 hx.1.2
    · simpa only [dist_eq_norm] using norm_sub_le_of_mem_same_dyadicCube hy.1.1 hy.1.2
  obtain ⟨n, hn, hlow, hupp⟩ := exists_spaceSplitting_distance_bin hroot hfar.1
  have han := (mem_Ioo.1 hn).1.le
  obtain ⟨P, hP, hxP⟩ := mem_iUnion₂.1 (hx.2.1 n han)
  obtain ⟨P', hP', hxP'⟩ := mem_iUnion₂.1 (hx.2.2 n han)
  obtain ⟨Q, hQ, hyQ⟩ := mem_iUnion₂.1 (hy.2.1 n han)
  obtain ⟨Q', hQ', hyQ'⟩ := mem_iUnion₂.1 (hy.2.2 n han)
  have hsep := spaceSplitting_comparable_bin_separated hxP hxP' hyQ hyQ' hfar.2 hlow hupp
  refine mem_iUnion₂.2 ⟨n, hn, ?_⟩
  constructor
  · exact mem_iUnion₂.2 ⟨(P, P'), mem_filter.2 ⟨mem_product.2 ⟨hP, hP'⟩, hsep.1⟩,
      ⟨hxP, hxP'⟩⟩
  · exact mem_iUnion₂.2 ⟨(Q, Q'), mem_filter.2 ⟨mem_product.2 ⟨hQ, hQ'⟩, hsep.2⟩,
      ⟨hyQ, hyQ'⟩⟩

theorem restrict_spaceSplittingFarComparable_le_depth_sum (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) (a p : ℕ) (X Y : Fin 2 → ℤ) :
    (spaceSplittingRootFourMeasure ρ a X Y).restrict (spaceSplittingFarComparableSet p) ≤
      ∑ n ∈ Finset.Ioo a (p + 12),
        (spaceSplittingRootFourMeasure ρ a X Y).restrict
          (spaceSplittingSeparatedCarrier ρ a n X ×ˢ
            spaceSplittingSeparatedCarrier ρ a n Y) := by
  apply (Measure.restrict_mono_ae
    (ae_spaceSplittingFarComparable_mem_depth_carrier ρ hρ a p X Y)).trans
  rw [← sum_attach (Finset.Ioo a (p + 12)), attach_eq_univ, ← Measure.sum_fintype]
  exact Measure.restrict_biUnion_le (Finset.countable_toSet _)

/-- Integration over genuine far comparable points is controlled by finite separated pairs. -/
theorem lintegral_spaceSplittingFarComparable_le_depth_sum (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) (a p : ℕ) (X Y : Fin 2 → ℤ)
    (f : (Plane × Plane) × (Plane × Plane) → ℝ≥0∞) :
    (∫⁻ z, f z ∂(spaceSplittingRootFourMeasure ρ a X Y).restrict
        (spaceSplittingFarComparableSet p)) ≤
      ∑ n ∈ Finset.Ioo a (p + 12),
        ∑ P ∈ spaceSplittingSeparatedPairs ρ a n X,
          ∑ Q ∈ spaceSplittingSeparatedPairs ρ a n Y,
            ∫⁻ z, f z
              ∂((ρ.restrict (dyadicCube n P.1)).prod (ρ.restrict (dyadicCube n P.2))).prod
                ((ρ.restrict (dyadicCube n Q.1)).prod (ρ.restrict (dyadicCube n Q.2))) := by
  apply (lintegral_mono' (restrict_spaceSplittingFarComparable_le_depth_sum ρ hρ a p X Y)
    (fun _ ↦ le_rfl)).trans_eq
  rw [lintegral_finsetSum_measure]
  apply sum_congr rfl
  intro n hn
  exact lintegral_restrict_spaceSplittingSeparatedCarriers_eq_sum ρ
    (Finset.mem_Ioo.1 hn).1.le X Y f

end FalconerThetaGauge
