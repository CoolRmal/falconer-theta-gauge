module

public import FalconerThetaGauge.DistanceMeasure
public import FalconerThetaGauge.RadialProjectionDefinitions
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-!
# The manuscript's weighted filtered distance measure

The density is the extended inverse square root of the Euclidean distance.
It is infinite on the diagonal, as required by the actual singular weight;
the separated carriers used later make it bounded almost everywhere.
The mask is a real Borel function with values in `[0,1]`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerThetaGauge

/-- The true weight `|x-y|^(-1/2)`, retaining its infinite diagonal value. -/
def crossDistanceWeight (p : Plane × Plane) : ℝ≥0∞ :=
  (ENNReal.ofReal (Real.sqrt (dist p.1 p.2)))⁻¹

@[fun_prop]
theorem measurable_crossDistanceWeight : Measurable crossDistanceWeight := by
  unfold crossDistanceWeight
  fun_prop

@[simp]
theorem crossDistanceWeight_diagonal (x : Plane) : crossDistanceWeight (x, x) = ∞ := by
  simp [crossDistanceWeight]

theorem crossDistanceWeight_pos (p : Plane × Plane) : 0 < crossDistanceWeight p := by
  exact ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top

theorem crossDistanceWeight_eq_ofReal {x y : Plane} (hxy : x ≠ y) :
    crossDistanceWeight (x, y) = ENNReal.ofReal ((Real.sqrt (dist x y))⁻¹) := by
  exact (ENNReal.ofReal_inv_of_pos (Real.sqrt_pos.2 (dist_pos.mpr hxy))).symm

/-- The unfiltered measure `α` of Definition 6.12, with the actual singular weight. -/
def weightedCrossDistanceMeasure (μ ν : Measure Plane) : Measure ℝ :=
  ((μ.prod ν).withDensity crossDistanceWeight).map
    (fun p : Plane × Plane ↦ dist p.1 p.2)

/-- The actual weighted pushforward after multiplying by a pair mask. -/
def filteredCrossDistanceMeasure (μ ν : Measure Plane) (m : Plane × Plane → ℝ) : Measure ℝ :=
  ((μ.prod ν).withDensity (fun p ↦ crossDistanceWeight p * ENNReal.ofReal (m p))).map
    (fun p : Plane × Plane ↦ dist p.1 p.2)

/-- The pair mask specified in Definition 6.12 from the two directional symbols. -/
def directionalPairMask (b₁ b₂ : Plane → UnitCircle → ℝ) (p : Plane × Plane) : ℝ :=
  b₁ p.1 (pairDirection p.1 p.2) * b₂ p.2 (pairDirection p.1 p.2)

@[fun_prop]
theorem measurable_pairDirection : Measurable (Function.uncurry pairDirection) := by
  unfold Function.uncurry pairDirection
  have h := measurable_radialProjection
  unfold Function.uncurry at h
  have h' := h.comp (measurable_swap : Measurable (Prod.swap : Plane × Plane → Plane × Plane))
  simpa only [Function.comp_def, Prod.swap] using h'

theorem measurable_directionalPairMask {b₁ b₂ : Plane → UnitCircle → ℝ}
    (h₁ : Measurable (Function.uncurry b₁)) (h₂ : Measurable (Function.uncurry b₂)) :
    Measurable (directionalPairMask b₁ b₂) := by
  unfold directionalPairMask
  exact (h₁.comp (measurable_fst.prodMk measurable_pairDirection)).mul
    (h₂.comp (measurable_snd.prodMk measurable_pairDirection))

theorem directionalPairMask_mem_Icc {b₁ b₂ : Plane → UnitCircle → ℝ}
    (h₁ : ∀ x w, b₁ x w ∈ Icc 0 1) (h₂ : ∀ x w, b₂ x w ∈ Icc 0 1)
    (p : Plane × Plane) : directionalPairMask b₁ b₂ p ∈ Icc 0 1 := by
  obtain ⟨h₁₀, h₁₁⟩ := h₁ p.1 (pairDirection p.1 p.2)
  obtain ⟨h₂₀, h₂₁⟩ := h₂ p.2 (pairDirection p.1 p.2)
  exact ⟨mul_nonneg h₁₀ h₂₀, by dsimp [directionalPairMask]; nlinarith⟩

/-- Every `[0,1]` mask produces a positive measure dominated by the actual `α`. -/
theorem filteredCrossDistanceMeasure_le (μ ν : Measure Plane) {m : Plane × Plane → ℝ}
    (hm : ∀ᵐ p ∂μ.prod ν, m p ≤ 1) :
    filteredCrossDistanceMeasure μ ν m ≤ weightedCrossDistanceMeasure μ ν := by
  apply Measure.map_mono _ continuous_dist.measurable
  apply withDensity_mono
  filter_upwards [hm] with p hp
  calc
    crossDistanceWeight p * ENNReal.ofReal (m p) ≤ crossDistanceWeight p * 1 :=
      mul_le_mul' le_rfl (by simpa using ENNReal.ofReal_le_ofReal hp)
    _ = crossDistanceWeight p := mul_one _

@[simp]
theorem weightedCrossDistanceMeasure_univ (μ ν : Measure Plane) :
    weightedCrossDistanceMeasure μ ν univ = ∫⁻ p, crossDistanceWeight p ∂μ.prod ν := by
  rw [weightedCrossDistanceMeasure, Measure.map_apply continuous_dist.measurable
    MeasurableSet.univ, preimage_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]

@[simp]
theorem filteredCrossDistanceMeasure_univ (μ ν : Measure Plane) (m : Plane × Plane → ℝ) :
    filteredCrossDistanceMeasure μ ν m univ =
      ∫⁻ p, crossDistanceWeight p * ENNReal.ofReal (m p) ∂μ.prod ν := by
  rw [filteredCrossDistanceMeasure, Measure.map_apply continuous_dist.measurable
    MeasurableSet.univ, preimage_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]

/-- An a.e. bound on the singular weight gives a finite unfiltered mass. -/
theorem weightedCrossDistanceMeasure_univ_le (μ ν : Measure Plane)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {W : ℝ≥0∞}
    (hW : ∀ᵐ p ∂μ.prod ν, crossDistanceWeight p ≤ W) :
    weightedCrossDistanceMeasure μ ν univ ≤ W := by
  rw [weightedCrossDistanceMeasure_univ]
  simpa using lintegral_mono_ae hW

/-- The removed weight is bounded by the weight bound times the actual excluded pair mass.
No positivity or finiteness of the excluded mass is hidden in this statement. -/
theorem filteredCrossDistanceMeasure_mass_loss_le (μ ν : Measure Plane)
    {m : Plane × Plane → ℝ} (hm : Measurable m) {Z : Set (Plane × Plane)}
    (hZ : MeasurableSet Z) {W : ℝ≥0∞}
    (hW : ∀ᵐ p ∂μ.prod ν, crossDistanceWeight p ≤ W)
    (hgood : ∀ᵐ p ∂μ.prod ν, p ∉ Z → m p = 1) :
    weightedCrossDistanceMeasure μ ν univ - filteredCrossDistanceMeasure μ ν m univ ≤
      W * μ.prod ν Z := by
  apply (tsub_le_iff_right).2
  rw [weightedCrossDistanceMeasure_univ, filteredCrossDistanceMeasure_univ]
  have hpoint : ∀ᵐ p ∂μ.prod ν,
      crossDistanceWeight p ≤
        crossDistanceWeight p * ENNReal.ofReal (m p) + Z.indicator (fun _ ↦ W) p := by
    filter_upwards [hW, hgood] with p hp hg
    by_cases hz : p ∈ Z
    · simpa only [indicator_of_mem hz] using le_add_of_le_right hp
    · simp [indicator_of_notMem hz, hg hz]
  calc
    ∫⁻ p, crossDistanceWeight p ∂μ.prod ν ≤
        ∫⁻ p, crossDistanceWeight p * ENNReal.ofReal (m p) +
          Z.indicator (fun _ ↦ W) p ∂μ.prod ν := lintegral_mono_ae hpoint
    _ = (∫⁻ p, crossDistanceWeight p * ENNReal.ofReal (m p) ∂μ.prod ν) +
        W * μ.prod ν Z := by
      have hf : Measurable (fun p ↦ crossDistanceWeight p * ENNReal.ofReal (m p)) := by
        fun_prop
      rw [lintegral_add_left hf,
        lintegral_indicator hZ, setLIntegral_const]
    _ = W * μ.prod ν Z + ∫⁻ p, crossDistanceWeight p * ENNReal.ofReal (m p) ∂μ.prod ν :=
      add_comm _ _

end FalconerThetaGauge
