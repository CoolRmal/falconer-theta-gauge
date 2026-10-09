module

public import FalconerThetaGauge.RadialProjectionLimitTails

/-!
# Lower logarithmic moments of the limiting density

Exponential density shells turn the cutoff bound into a summable polynomial
majorant. Two spare logarithmic powers suffice to retain every requested
lower Orlicz moment of the actual limiting Radon–Nikodym density.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace FalconerThetaGauge

theorem log_exp_one_add_le_of_le_exp {t q : ℝ} (hq : 1 ≤ q)
    (ht0 : 0 ≤ t) (ht : t ≤ 2 * Real.exp q) : Real.log (Real.exp 1 + t) ≤ q + 2 := by
  have he : Real.exp 1 ≤ Real.exp q := Real.exp_le_exp.mpr hq
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by
    have h := Real.add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0)
    linarith
  calc
      Real.log (Real.exp 1 + t) ≤ Real.log (Real.exp (q + 2)) := by
        apply Real.log_le_log (add_pos_of_pos_of_nonneg (Real.exp_pos 1) ht0)
        rw [Real.exp_add]
        nlinarith [Real.exp_pos q]
      _ = q + 2 := Real.log_exp _

/-- Exponential density shells cover the real nonnegative half line. -/
theorem exists_exponential_density_shell {t : ℝ} (ht : 2 * Real.exp 1 < t) :
    ∃ n : ℕ, 2 * Real.exp ((n : ℝ) + 1) < t ∧ t ≤ 2 * Real.exp ((n : ℝ) + 2) := by
  have hex : ∃ n : ℕ, t ≤ 2 * Real.exp ((n : ℝ) + 1) := by
    obtain ⟨n, hn⟩ := exists_nat_gt (Real.log (t / 2))
    refine ⟨n, ?_⟩
    have htpos : 0 < t / 2 := by linarith [Real.exp_pos 1]
    have h := Real.exp_le_exp.mpr (show Real.log (t / 2) ≤ (n : ℝ) + 1 by linarith)
    rw [Real.exp_log htpos] at h
    linarith
  have hspec := Nat.find_spec hex
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with hzero | hpos
    · simp only [hzero, Nat.cast_zero, zero_add] at hspec
      exact (not_le_of_gt ht hspec).elim
    · exact hpos
  have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
  refine ⟨Nat.find hex - 1, not_le.mp hmin, ?_⟩
  have hcast : ((Nat.find hex - 1 : ℕ) : ℝ) + 2 = (Nat.find hex : ℝ) + 1 := by
    have hnat : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    have h := congrArg (fun m : ℕ ↦ (m : ℝ)) hnat
    push_cast at h
    linarith
  simpa only [hcast] using hspec

/-- The cutoff bound gives a finite lower Orlicz moment for an actual real density. -/
theorem lintegral_orliczPhiENN_ne_top_of_cutoff {α : Type*} [MeasurableSpace α]
    (σ ξ : Measure α) [IsFiniteMeasure σ] {f : α → ℝ}
    (hf : Measurable f) (hfnonneg : ∀ x, 0 ≤ f x)
    (hdensity : ξ.withDensity (fun x ↦ ENNReal.ofReal (f x)) = σ)
    {γ : ℝ} (hγ : 0 ≤ γ) {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hcutoff : ∀ H : ℝ, 0 < H → ∀ A : Set α,
      σ A ≤ ENNReal.ofReal H * ξ A + orliczTailCoefficient (γ + 2) H * K) :
    (∫⁻ x, orliczPhiENN γ (f x) ∂ξ) ≠ ∞ := by
  classical
  let g : α → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (Real.log (Real.exp 1 + f x) ^ γ)
  have hg : Measurable g := by fun_prop
  have heq : (∫⁻ x, orliczPhiENN γ (f x) ∂ξ) = ∫⁻ x, g x ∂σ := by
    rw [← hdensity, lintegral_withDensity_eq_lintegral_mul ξ (by fun_prop) hg]
    congr 1
    funext x
    simp only [orliczPhiENN, orliczPhi, Pi.mul_apply, g]
    exact ENNReal.ofReal_mul (hfnonneg x)
  rw [heq]
  let B : Set α := {x | f x ≤ 2 * Real.exp 1}
  let A : ℕ → Set α := fun n ↦
    {x | 2 * Real.exp ((n : ℝ) + 1) < f x ∧ f x ≤ 2 * Real.exp ((n : ℝ) + 2)}
  have hA : ∀ n, MeasurableSet (A n) := fun n ↦
    (measurableSet_lt measurable_const hf).inter (measurableSet_le hf measurable_const)
  have hB : MeasurableSet B := measurableSet_le hf measurable_const
  have hcover : (univ : Set α) ⊆ B ∪ ⋃ n, A n := by
    intro x _
    rcases le_or_gt (f x) (2 * Real.exp 1) with hx | hx
    · exact Or.inl hx
    · obtain ⟨n, hn⟩ := exists_exponential_density_shell hx
      exact Or.inr (mem_iUnion.mpr ⟨n, hn⟩)
  have hbase : ∫⁻ x in B, g x ∂σ ≤ ENNReal.ofReal ((3 : ℝ) ^ γ) * σ univ := by
    calc
      ∫⁻ x in B, g x ∂σ ≤ ∫⁻ x in B, ENNReal.ofReal ((3 : ℝ) ^ γ) ∂σ := by
        apply setLIntegral_mono' hB
        intro x hx
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow
          (zero_le_one.trans (log_exp_one_add_ge_one (hfnonneg x)))
          (by convert log_exp_one_add_le_of_le_exp (q := 1) le_rfl (hfnonneg x) hx using 1; norm_num) hγ)
      _ = ENNReal.ofReal ((3 : ℝ) ^ γ) * σ B := setLIntegral_const _ _
      _ ≤ _ := by gcongr; exact subset_univ B
  have hann : ∀ n, ∫⁻ x in A n, g x ∂σ ≤
      2 * K * ENNReal.ofReal (((n : ℝ) + 4) ^ γ * ((n : ℝ) + 1) ^ (-(γ + 2))) := by
    intro n
    have hlog : ∀ x ∈ A n, g x ≤ ENNReal.ofReal (((n : ℝ) + 4) ^ γ) := by
      intro x hx
      have hq : (1 : ℝ) ≤ (n : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
      have hl := log_exp_one_add_le_of_le_exp hq (hfnonneg x) hx.2
      have hl' : Real.log (Real.exp 1 + f x) ≤ (n : ℝ) + 4 := by linarith
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow
        (zero_le_one.trans (log_exp_one_add_ge_one (hfnonneg x)))
        hl' hγ)
    have htail : σ (A n) ≤ 2 *
        (ENNReal.ofReal (((n : ℝ) + 1) ^ (-(γ + 2))) * K) := by
      have hbound := measure_density_tail_le σ ξ (hf.ennreal_ofReal) hdensity hcutoff
        (Real.exp_pos ((n : ℝ) + 1))
      have hsub : A n ⊆ {x | ENNReal.ofReal (2 * Real.exp ((n : ℝ) + 1)) <
          ENNReal.ofReal (f x)} := by
        intro x hx
        have hx' : 2 * Real.exp ((n : ℝ) + 1) < f x := hx.1
        exact ENNReal.ofReal_lt_ofReal_iff
          (by linarith [Real.exp_pos ((n : ℝ) + 1)]) |>.mpr hx'
      refine (measure_mono hsub).trans (hbound.trans ?_)
      gcongr
      exact orliczTailCoefficient_exp_le (by linarith) n
    calc
      ∫⁻ x in A n, g x ∂σ ≤ ∫⁻ x in A n, ENNReal.ofReal (((n : ℝ) + 4) ^ γ) ∂σ :=
        setLIntegral_mono' (hA n) hlog
      _ = ENNReal.ofReal (((n : ℝ) + 4) ^ γ) * σ (A n) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (((n : ℝ) + 4) ^ γ) *
          (2 * (ENNReal.ofReal (((n : ℝ) + 1) ^ (-(γ + 2))) * K)) :=
        by gcongr
      _ = _ := by rw [ENNReal.ofReal_mul (by positivity)]; ac_rfl
  have hle : ∫⁻ x, g x ∂σ ≤ ENNReal.ofReal ((3 : ℝ) ^ γ) * σ univ +
      2 * K * ∑' n : ℕ,
        ENNReal.ofReal (((n : ℝ) + 4) ^ γ * ((n : ℝ) + 1) ^ (-(γ + 2))) := by
    calc
      ∫⁻ x, g x ∂σ = ∫⁻ x in univ, g x ∂σ := by rw [Measure.restrict_univ]
      _ ≤ ∫⁻ x in B ∪ ⋃ n, A n, g x ∂σ := lintegral_mono_set hcover
      _ ≤ (∫⁻ x in B, g x ∂σ) + ∫⁻ x in ⋃ n, A n, g x ∂σ := lintegral_union_le _ _ _
      _ ≤ ENNReal.ofReal ((3 : ℝ) ^ γ) * σ univ + ∑' n, ∫⁻ x in A n, g x ∂σ :=
        add_le_add hbase (lintegral_iUnion_le _ _)
      _ ≤ ENNReal.ofReal ((3 : ℝ) ^ γ) * σ univ + ∑' n : ℕ, 2 * K *
          ENNReal.ofReal (((n : ℝ) + 4) ^ γ * ((n : ℝ) + 1) ^ (-(γ + 2))) :=
        add_le_add le_rfl (ENNReal.tsum_le_tsum hann)
      _ = _ := by rw [ENNReal.tsum_mul_left]
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _),
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hK)
        (summable_orlicz_tail_majorant hγ).tsum_ofReal_ne_top⟩) hle

/-- The retained Orlicz moment belongs to the actual Radon–Nikodym derivative. -/
theorem lintegral_orliczPhiExtended_rnDeriv_ne_top_of_cutoff {α : Type*} [MeasurableSpace α]
    (σ ξ : Measure α) [IsFiniteMeasure σ] [SigmaFinite ξ] (hac : σ ≪ ξ)
    {γ : ℝ} (hγ : 0 ≤ γ) {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hcutoff : ∀ H : ℝ, 0 < H → ∀ A : Set α,
      σ A ≤ ENNReal.ofReal H * ξ A + orliczTailCoefficient (γ + 2) H * K) :
    (∫⁻ x, orliczPhiExtended γ (σ.rnDeriv ξ x) ∂ξ) ≠ ∞ := by
  have hfinite := Measure.rnDeriv_ne_top σ ξ
  have hdensity : ξ.withDensity (fun x ↦ ENNReal.ofReal ((σ.rnDeriv ξ x).toReal)) = σ := by
    refine (withDensity_congr_ae ?_).trans (Measure.withDensity_rnDeriv_eq σ ξ hac)
    filter_upwards [hfinite] with x hx
    exact ENNReal.ofReal_toReal hx
  have hbound := lintegral_orliczPhiENN_ne_top_of_cutoff σ ξ
    (Measure.measurable_rnDeriv σ ξ).ennreal_toReal
    (fun x ↦ ENNReal.toReal_nonneg) hdensity hγ hK hcutoff
  have heq : (∫⁻ x, orliczPhiExtended γ (σ.rnDeriv ξ x) ∂ξ) =
      ∫⁻ x, orliczPhiENN γ ((σ.rnDeriv ξ x).toReal) ∂ξ := by
    apply lintegral_congr_ae
    filter_upwards [hfinite] with x hx
    simp only [orliczPhiExtended, ite_eq_right hx]
  rwa [heq]

/-- A weak probability limit of densities with a stronger logarithmic moment
has a density with a finite requested lower Orlicz moment. -/
theorem weak_limit_orlicz_density {α : Type*}
    [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
    [HasOuterApproxClosed α] (ξ : Measure α) [ξ.OuterRegular] [SigmaFinite ξ]
    {σ : ProbabilityMeasure α} {σn : ℕ → ProbabilityMeasure α}
    {fn : ℕ → α → ℝ≥0∞} {γ : ℝ} (hγ : 0 ≤ γ) {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hdensity : ∀ n, (σn n : Measure α) = ξ.withDensity (fn n))
    (hbound : ∀ n, (∫⁻ x, orliczPhiExtended (γ + 2) (fn n x) ∂ξ) ≤ K)
    (hconv : Tendsto σn atTop (𝓝 σ)) :
    (σ : Measure α) ≪ ξ ∧
      (∫⁻ x, orliczPhiExtended γ ((σ : Measure α).rnDeriv ξ x) ∂ξ) ≠ ∞ := by
  have hp : 0 < γ + 2 := by linarith
  have hac := absolutelyContinuous_of_tendsto_of_uniform_orlicz ξ hp hK hdensity hbound hconv
  refine ⟨hac, lintegral_orliczPhiExtended_rnDeriv_ne_top_of_cutoff
    (σ : Measure α) ξ hac hγ hK ?_⟩
  intro H hH A
  exact measure_le_cutoff_of_tendsto_of_orlicz ξ hp.le hdensity hbound hconv hH A

end FalconerThetaGauge
