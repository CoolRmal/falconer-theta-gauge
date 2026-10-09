module

public import FalconerThetaGauge.SpaceSplittingRadialPower
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Genuine real radial powers for the separated-scale stationary terms -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Finset
open scoped ContDiff Topology

namespace FalconerThetaGauge

theorem iteratedDeriv_real_rpow (α : ℝ) (k : ℕ) (r : ℝ) :
    iteratedDeriv k (fun x : ℝ ↦ x ^ α) r =
      (∏ l ∈ range k, (α - l)) * r ^ (α - k) := by
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const, descPochhammer_eval_eq_prod_range]

theorem iteratedDeriv_ofReal_rpow (α : ℝ) (k : ℕ) {r : ℝ} (hr : r ≠ 0) :
    iteratedDeriv k (fun x : ℝ ↦ ((x ^ α : ℝ) : ℂ)) r =
      (((∏ l ∈ range k, (α - l)) * r ^ (α - k) : ℝ) : ℂ) := by
  rw [iteratedDeriv_ofReal_eq
    ((Real.contDiffAt_rpow_const_of_ne (n := ∞) hr).of_le (by simp)),
    iteratedDeriv_real_rpow]

/-- The actual source amplitude with the real stationary exponent, not an integer surrogate. -/
def spaceSplittingRealPowerAmplitude (K v : ℕ) (α : ℝ) (r : ℝ) : ℂ :=
  ((((2 : ℝ) ^ v)⁻¹ : ℝ) : ℂ) * (maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) : ℂ) *
    ((r ^ α : ℝ) : ℂ)

theorem spaceSplittingRealPowerAmplitude_eq_zero (K v : ℕ) (α : ℝ) {r : ℝ}
    (hr : r ∉ Set.Icc ((2 : ℝ) ^ v / 4) (4 * (2 : ℝ) ^ v)) :
    spaceSplittingRealPowerAmplitude K v α r = 0 := by
  have hs : (0 : ℝ) < 2 ^ v := by positivity
  have hnot : r / (2 : ℝ) ^ v ∉ Set.Icc (1 / 4) 4 := by
    intro hm
    apply hr
    constructor
    · have h := (le_div_iff₀ hs).mp hm.1
      linarith
    · exact (div_le_iff₀ hs).mp hm.2
  simp only [spaceSplittingRealPowerAmplitude, maskedFrequencyCutoff_eq_zero K hnot,
    Complex.ofReal_zero, mul_zero, zero_mul]

theorem tsupport_spaceSplittingRealPowerAmplitude_subset (K v : ℕ) (α : ℝ) :
    tsupport (spaceSplittingRealPowerAmplitude K v α) ⊆
      Set.Icc ((2 : ℝ) ^ v / 4) (4 * (2 : ℝ) ^ v) := by
  apply isClosed_Icc.closure_subset_iff.mpr
  intro r hr
  by_contra hnot
  exact hr (spaceSplittingRealPowerAmplitude_eq_zero K v α hnot)

theorem hasCompactSupport_spaceSplittingRealPowerAmplitude (K v : ℕ) (α : ℝ) :
    HasCompactSupport (spaceSplittingRealPowerAmplitude K v α) :=
  HasCompactSupport.intro isCompact_Icc fun _ hr ↦
    spaceSplittingRealPowerAmplitude_eq_zero K v α hr

theorem contDiff_spaceSplittingRealPowerAmplitude (K v : ℕ) (α : ℝ) :
    ContDiff ℝ ∞ (spaceSplittingRealPowerAmplitude K v α) := by
  apply contDiff_iff_contDiffAt.mpr
  intro r
  by_cases hr : r = 0
  · subst r
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    have hn : Iio ((2 : ℝ) ^ v / 4) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (by positivity)
    filter_upwards [hn] with x hx
    exact spaceSplittingRealPowerAmplitude_eq_zero K v α (fun h ↦ not_le_of_gt hx h.1)
  · unfold spaceSplittingRealPowerAmplitude
    apply (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp r
      (((contDiff_maskedFrequencyCutoff K).contDiffAt).comp r
        (contDiffAt_id.div_const _)))).mul
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp r (Real.contDiffAt_rpow_const_of_ne hr)

theorem volume_tsupport_spaceSplittingRealPowerAmplitude_le (K v : ℕ) (α : ℝ) :
    volume.real (tsupport (spaceSplittingRealPowerAmplitude K v α)) ≤ 4 * (2 : ℝ) ^ v := by
  calc
    _ ≤ volume.real (Set.Icc ((2 : ℝ) ^ v / 4) (4 * (2 : ℝ) ^ v)) :=
      measureReal_mono (tsupport_spaceSplittingRealPowerAmplitude_subset K v α)
        (by simp)
    _ = 4 * (2 : ℝ) ^ v - (2 : ℝ) ^ v / 4 := by
      have hs : (0 : ℝ) < 2 ^ v := by positivity
      rw [Real.volume_real_Icc_of_le (by linarith)]
    _ ≤ _ := by
      have hs : (0 : ℝ) < 2 ^ v := by positivity
      linarith

end FalconerThetaGauge
