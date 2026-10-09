module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Integral.Regular
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Absolute continuity from a reconstructed pairing

An absolutely continuous error measure plus a square-root open-set bound
forces absolute continuity. Smooth Schwartz cutoffs connect a reconstructed
test-function pairing to that open-set estimate.

The cutoff construction and square-root argument are adapted from
`FalconerPacking.SchwartzDensityCriterion` and `FalconerPacking.WeakDensityLimit`,
by Yongxi Lin, Apache-2.0, commit `70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/tree/70140ccedfb6de71342299523a21b1550df69ab9
The additive error-measure extension is proved here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology FourierTransform
open scoped ENNReal ContDiff

namespace FalconerThetaGauge

/-- An absolutely continuous error measure can be added to a positive-power
open-set bound without losing absolute continuity. -/
theorem absolutelyContinuous_of_open_bound_with_error
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    {μ ν σ : Measure α} [ν.OuterRegular] [σ.OuterRegular]
    (hσ : σ ≪ ν) {C : ℝ≥0∞} (hC : C ≠ ⊤) {s : ℝ} (hs : 0 < s)
    (hbound : ∀ U : Set α, IsOpen U → μ U ≤ σ U + C * ν U ^ s) : μ ≪ ν := by
  intro A hA
  apply le_antisymm _ zero_le
  have hσA : σ A = 0 := hσ hA
  have := ENNReal.nhdsGT_zero_neBot
  have hlim : Tendsto (fun ε : ℝ≥0∞ ↦ ε + C * ε ^ s) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_add, id_eq] using
      (tendsto_id.mono_left nhdsWithin_le_nhds).add
        ((ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hC hs).mono_left
          nhdsWithin_le_nhds)
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  obtain ⟨U, hAU, hU, hUε⟩ := A.exists_isOpen_lt_of_lt (μ := ν) ε
    (by simpa only [hA, mem_Ioi] using hε)
  obtain ⟨V, hAV, hV, hVε⟩ := A.exists_isOpen_lt_of_lt (μ := σ) ε
    (by simpa only [hσA, mem_Ioi] using hε)
  have hAW : A ⊆ U ∩ V := fun x hx ↦ ⟨hAU hx, hAV hx⟩
  exact (measure_mono hAW).trans ((hbound (U ∩ V) (hU.inter hV)).trans
    (add_le_add ((measure_mono inter_subset_right).trans hVε.le)
      (mul_le_mul' le_rfl
        (ENNReal.rpow_le_rpow ((measure_mono inter_subset_left).trans hUε.le) hs.le))))

/-- A compact subset of an open real set admits a smooth compact cutoff. -/
theorem exists_smooth_compact_cutoff {K U : Set ℝ} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      EqOn f 1 K ∧ EqOn f 0 Uᶜ ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨R, _, hKR⟩ := hK.isBounded.subset_ball_lt 0 (0 : ℝ)
  let V : Set ℝ := U ∩ Metric.ball 0 R
  have hV : IsOpen V := hU.inter Metric.isOpen_ball
  have hKV : K ⊆ V := fun x hx ↦ ⟨hKU hx, hKR hx⟩
  obtain ⟨f, hfzero, hfone, hfrange⟩ := exists_contMDiffMap_zero_one_of_isClosed
    (modelWithCornersSelf ℝ ℝ) hV.isClosed_compl hK.isClosed
    (disjoint_compl_left_iff_subset.mpr hKV) (n := ⊤)
  have hsupp : Function.support f ⊆ Metric.closedBall (0 : ℝ) R := by
    intro x hx
    by_cases hxV : x ∈ V
    · exact Metric.ball_subset_closedBall hxV.2
    · exact False.elim (hx (hfzero hxV))
  have hfcompact : HasCompactSupport (f : ℝ → ℝ) :=
    (isCompact_closedBall (0 : ℝ) R).of_isClosed_subset isClosed_closure
      (closure_minimal hsupp Metric.isClosed_closedBall)
  refine ⟨f, f.contMDiff.contDiff, hfcompact, hfone, ?_, hfrange⟩
  intro x hx
  exact hfzero (fun hxV ↦ hx hxV.1)

private theorem schwartz_cutoff_eLpNorm_le {φ : SchwartzMap ℝ ℂ} {U : Set ℝ}
    (hU : MeasurableSet U) (hzero : ∀ x ∉ U, φ x = 0) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    eLpNorm (φ : ℝ → ℂ) 2 volume ≤ volume U ^ (1 / 2 : ℝ) := by
  have hmono : eLpNorm (φ : ℝ → ℂ) 2 volume ≤
      eLpNorm (U.indicator (fun _ : ℝ ↦ (1 : ℝ))) 2 volume := by
    apply eLpNorm_mono_ae φ.continuous.aestronglyMeasurable
    filter_upwards [] with x
    by_cases hx : x ∈ U
    · simpa only [indicator_of_mem hx, norm_one] using hbound x
    · simp only [hzero x hx, norm_zero, indicator_of_notMem hx, norm_zero, le_refl]
  have heq := eLpNorm_indicator_const (μ := (volume : Measure ℝ))
    (c := (1 : ℝ)) hU.nullMeasurableSet (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  norm_num at heq
  rwa [heq] at hmono

/-- A reconstructed Schwartz pairing bounds compact masses by the absolutely
continuous error mass plus the square-root term from the L² component. -/
theorem compact_mass_le_of_schwartz_bound_with_error
    {μ σ : Measure ℝ} [IsFiniteMeasure μ] {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ φ : SchwartzMap ℝ ℂ,
      ‖∫ x, φ x ∂μ‖ ≤ (∫ x, ‖φ x‖ ∂σ) + C * ‖φ.toLp 2 volume‖)
    {K U : Set ℝ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    μ K ≤ σ U + ENNReal.ofReal C * volume U ^ (1 / 2 : ℝ) := by
  obtain ⟨f, hfsmooth, hfcompact, hfone, hfzero, hfrange⟩ :=
    exists_smooth_compact_cutoff hK hU hKU
  have hfc : HasCompactSupport (fun x ↦ (f x : ℂ)) :=
    hfcompact.comp_left Complex.ofReal_zero
  let φ : SchwartzMap ℝ ℂ :=
    hfc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hfsmooth)
  have hφ : ∀ x, φ x = (f x : ℂ) := fun _ ↦ rfl
  have hnorm : eLpNorm (φ : ℝ → ℂ) 2 volume ≤ volume U ^ (1 / 2 : ℝ) := by
    apply schwartz_cutoff_eLpNorm_le hU.measurableSet
    · intro x hx
      simp only [hφ, hfzero hx, Pi.zero_apply, Complex.ofReal_zero]
    · intro x
      simpa only [hφ, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hfrange x).1] using (hfrange x).2
  have hpair := hbound φ
  have hint : (∫ x, φ x ∂μ) = (∫ x, f x ∂μ : ℝ) := integral_complex_ofReal
  rw [hint, Complex.norm_real, Real.norm_eq_abs] at hpair
  have herror : ENNReal.ofReal (∫ x, ‖φ x‖ ∂σ) ≤ σ U := by
    apply integral_le_measure
    · intro x _
      simpa only [hφ, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hfrange x).1] using (hfrange x).2
    · intro x hx
      simp only [hφ, hfzero hx, Pi.zero_apply, Complex.ofReal_zero, norm_zero, le_refl]
  calc
    μ K ≤ ENNReal.ofReal (∫ x, f x ∂μ) :=
      (hfsmooth.continuous.integrable_of_hasCompactSupport hfcompact).measure_le_integral
        (Eventually.of_forall fun x ↦ (hfrange x).1) (fun x hx ↦ (hfone hx).ge)
    _ ≤ ENNReal.ofReal ((∫ x, ‖φ x‖ ∂σ) + C * ‖φ.toLp 2 volume‖) :=
      ENNReal.ofReal_le_ofReal ((le_abs_self _).trans hpair)
    _ ≤ ENNReal.ofReal (∫ x, ‖φ x‖ ∂σ) +
        ENNReal.ofReal (C * ‖φ.toLp 2 volume‖) := ENNReal.ofReal_add_le
    _ ≤ σ U + ENNReal.ofReal C * volume U ^ (1 / 2 : ℝ) := by
      rw [ENNReal.ofReal_mul hC, SchwartzMap.norm_toLp,
        ENNReal.ofReal_toReal (φ.eLpNorm_lt_top 2 volume).ne]
      exact add_le_add herror (mul_le_mul' le_rfl hnorm)

/-- The pairing reconstructed from an absolutely continuous error measure and
an L²-bounded component is absolutely continuous. -/
theorem absolutelyContinuous_of_schwartz_bound_with_error
    {μ σ : Measure ℝ} [IsFiniteMeasure μ] [σ.OuterRegular]
    (hσ : σ ≪ volume) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ φ : SchwartzMap ℝ ℂ,
      ‖∫ x, φ x ∂μ‖ ≤ (∫ x, ‖φ x‖ ∂σ) + C * ‖φ.toLp 2 volume‖) : μ ≪ volume := by
  apply absolutelyContinuous_of_open_bound_with_error hσ ENNReal.ofReal_ne_top
    (by norm_num : (0 : ℝ) < 1 / 2)
  intro U hU
  rw [hU.measure_eq_iSup_isCompact μ]
  exact iSup_le fun K ↦ iSup_le fun hKU ↦ iSup_le fun hK ↦
    compact_mass_le_of_schwartz_bound_with_error hC hbound hK hU hKU

/-- A Schwartz function and an L² function satisfy the usual Cauchy–Schwarz
bound for their integral pairing. -/
theorem schwartz_integral_mul_l2_le (φ : SchwartzMap ℝ ℂ) (g : Lp ℂ 2 volume) :
    ‖∫ x, φ x * g x ∂volume‖ ≤ ‖φ.toLp 2 volume‖ * ‖g‖ := by
  have htwo : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hg : ‖g‖ = (∫ x, ‖g x‖ ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) := by
    rw [Lp.norm_def, (Lp.memLp g).eLpNorm_eq_integral_rpow_norm
      (by norm_num) (by norm_num)]
    norm_num only [ENNReal.toReal_ofNat, inv_eq_one_div]
    rw [ENNReal.toReal_ofReal (by positivity)]
  calc
    ‖∫ x, φ x * g x ∂volume‖ ≤ ∫ x, ‖φ x * g x‖ ∂volume :=
      norm_integral_le_integral_norm _
    _ = ∫ x, ‖φ x‖ * ‖g x‖ ∂volume := by simp only [norm_mul]
    _ ≤ (∫ x, ‖φ x‖ ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) *
        (∫ x, ‖g x‖ ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) := by
      apply integral_mul_norm_le_Lp_mul_Lq htwo
      · simpa using φ.memLp 2 volume
      · simpa using Lp.memLp g
    _ = ‖φ.toLp 2 volume‖ * ‖g‖ := by
      rw [hg, SchwartzMap.norm_toLp' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
      norm_num

/-- A finite positive measure represented on Schwartz functions by an L¹ error
and an L² component is absolutely continuous with respect to Lebesgue measure. -/
theorem absolutelyContinuous_of_l1_l2_schwartz_pairing
    {μ : Measure ℝ} [IsFiniteMeasure μ] {f : ℝ → ℂ} (hf : Integrable f volume)
    (g : Lp ℂ 2 volume)
    (hpair : ∀ φ : SchwartzMap ℝ ℂ,
      (∫ x, φ x ∂μ) = (∫ x, φ x * f x ∂volume) + (∫ x, φ x * g x ∂volume)) :
    μ ≪ volume := by
  let σ : Measure ℝ := volume.withDensity (fun x ↦ ENNReal.ofReal ‖f x‖)
  have : IsFiniteMeasure σ := isFiniteMeasure_withDensity_ofReal hf.norm.hasFiniteIntegral
  apply absolutelyContinuous_of_schwartz_bound_with_error
    (σ := σ) (withDensity_absolutelyContinuous _ _) (norm_nonneg g)
  intro φ
  have herror : (∫ x, ‖φ x‖ ∂σ) = ∫ x, ‖φ x‖ * ‖f x‖ ∂volume := by
    rw [integral_withDensity_eq_integral_toReal_smul₀
      hf.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) (fun x ↦ ‖φ x‖)]
    simp only [ENNReal.toReal_ofReal (norm_nonneg _), smul_eq_mul, mul_comm]
  rw [hpair φ, herror]
  calc
    ‖(∫ x, φ x * f x ∂volume) + (∫ x, φ x * g x ∂volume)‖ ≤
        ‖∫ x, φ x * f x ∂volume‖ + ‖∫ x, φ x * g x ∂volume‖ := norm_add_le _ _
    _ ≤ (∫ x, ‖φ x * f x‖ ∂volume) + ‖φ.toLp 2 volume‖ * ‖g‖ :=
      add_le_add (norm_integral_le_integral_norm _) (schwartz_integral_mul_l2_le φ g)
    _ = (∫ x, ‖φ x‖ * ‖f x‖ ∂volume) + ‖g‖ * ‖φ.toLp 2 volume‖ := by
      simp only [norm_mul, mul_comm]

/-- The inverse Fourier transform preserves the L² norm of a Schwartz test. -/
theorem schwartz_fourierInv_l2_norm (φ : SchwartzMap ℝ ℂ) :
    ‖(𝓕⁻ φ).toLp 2 volume‖ = ‖φ.toLp 2 volume‖ := by
  simpa using (SchwartzMap.norm_fourier_toL2_eq (𝓕⁻ φ)).symm

/-- Frequency-space L² reconstruction together with a spatial L¹ error also
forces absolute continuity; Plancherel supplies the test-function bound. -/
theorem absolutelyContinuous_of_l1_fourier_l2_schwartz_pairing
    {μ : Measure ℝ} [IsFiniteMeasure μ] {f : ℝ → ℂ} (hf : Integrable f volume)
    (g : Lp ℂ 2 volume)
    (hpair : ∀ φ : SchwartzMap ℝ ℂ,
      (∫ x, φ x ∂μ) = (∫ x, φ x * f x ∂volume) +
        (∫ ξ, (𝓕⁻ φ) ξ * g ξ ∂volume)) : μ ≪ volume := by
  let σ : Measure ℝ := volume.withDensity (fun x ↦ ENNReal.ofReal ‖f x‖)
  have : IsFiniteMeasure σ := isFiniteMeasure_withDensity_ofReal hf.norm.hasFiniteIntegral
  apply absolutelyContinuous_of_schwartz_bound_with_error
    (σ := σ) (withDensity_absolutelyContinuous _ _) (norm_nonneg g)
  intro φ
  have herror : (∫ x, ‖φ x‖ ∂σ) = ∫ x, ‖φ x‖ * ‖f x‖ ∂volume := by
    rw [integral_withDensity_eq_integral_toReal_smul₀
      hf.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) (fun x ↦ ‖φ x‖)]
    simp only [ENNReal.toReal_ofReal (norm_nonneg _), smul_eq_mul, mul_comm]
  rw [hpair φ, herror]
  calc
    ‖(∫ x, φ x * f x ∂volume) + (∫ ξ, (𝓕⁻ φ) ξ * g ξ ∂volume)‖ ≤
        ‖∫ x, φ x * f x ∂volume‖ + ‖∫ ξ, (𝓕⁻ φ) ξ * g ξ ∂volume‖ := norm_add_le _ _
    _ ≤ (∫ x, ‖φ x * f x‖ ∂volume) + ‖(𝓕⁻ φ).toLp 2 volume‖ * ‖g‖ :=
      add_le_add (norm_integral_le_integral_norm _) (schwartz_integral_mul_l2_le (𝓕⁻ φ) g)
    _ = (∫ x, ‖φ x‖ * ‖f x‖ ∂volume) + ‖g‖ * ‖φ.toLp 2 volume‖ := by
      simp only [norm_mul, schwartz_fourierInv_l2_norm, mul_comm]

end FalconerThetaGauge
