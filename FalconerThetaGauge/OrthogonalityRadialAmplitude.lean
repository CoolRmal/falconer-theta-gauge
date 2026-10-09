module

public import FalconerThetaGauge.MaskedFourierEnergyCutoff
public import FalconerThetaGauge.LinearPhase

/-! # The literal source radial amplitude and its compact dyadic support -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace FalconerThetaGauge

/-- The actual radial weight `2⁻ᵛ Ψ(r/2ᵛ) r²` in Estimate 7.6. -/
def orthogonalityRadialAmplitude (K v : ℕ) (r : ℝ) : ℂ :=
  (((2 : ℝ) ^ v)⁻¹ : ℂ) * (maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) : ℂ) * (r : ℂ) ^ 2

theorem contDiff_orthogonalityRadialAmplitude (K v : ℕ) :
    ContDiff ℝ ∞ (orthogonalityRadialAmplitude K v) := by
  unfold orthogonalityRadialAmplitude
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    ((contDiff_maskedFrequencyCutoff K).comp (contDiff_id.div_const _)))).mul
      (Complex.ofRealCLM.contDiff.pow 2)

theorem orthogonalityRadialAmplitude_eq_zero (K v : ℕ) {r : ℝ}
    (hr : r ∉ Icc ((2 : ℝ) ^ v / 4) (4 * (2 : ℝ) ^ v)) :
    orthogonalityRadialAmplitude K v r = 0 := by
  have hs : (0 : ℝ) < 2 ^ v := by positivity
  have hnot : r / (2 : ℝ) ^ v ∉ Icc (1 / 4) 4 := by
    intro hm
    apply hr
    constructor
    · have h := (le_div_iff₀ hs).mp hm.1
      linarith
    · exact (div_le_iff₀ hs).mp hm.2
  simp only [orthogonalityRadialAmplitude, maskedFrequencyCutoff_eq_zero K hnot,
    Complex.ofReal_zero, mul_zero, zero_mul]

theorem tsupport_orthogonalityRadialAmplitude_subset (K v : ℕ) :
    tsupport (orthogonalityRadialAmplitude K v) ⊆
      Icc ((2 : ℝ) ^ v / 4) (4 * (2 : ℝ) ^ v) := by
  apply isClosed_Icc.closure_subset_iff.mpr
  intro r hr
  by_contra hnot
  exact hr (orthogonalityRadialAmplitude_eq_zero K v hnot)

theorem hasCompactSupport_orthogonalityRadialAmplitude (K v : ℕ) :
    HasCompactSupport (orthogonalityRadialAmplitude K v) :=
  HasCompactSupport.intro isCompact_Icc fun _ hr ↦
    orthogonalityRadialAmplitude_eq_zero K v hr

theorem volume_tsupport_orthogonalityRadialAmplitude_le (K v : ℕ) :
    volume.real (tsupport (orthogonalityRadialAmplitude K v)) ≤ 4 * (2 : ℝ) ^ v := by
  have hs : (0 : ℝ) < 2 ^ v := by positivity
  have h := measureReal_mono (μ := volume) (tsupport_orthogonalityRadialAmplitude_subset K v)
    (isCompact_Icc.measure_ne_top)
  rw [Real.volume_real_Icc_of_le (by linarith : (2 : ℝ) ^ v / 4 ≤ 4 * (2 : ℝ) ^ v)] at h
  exact h.trans (by linarith)

theorem norm_iteratedDeriv_maskedFrequencyCutoff_le_geometric {T K j : ℕ}
    (hK : 6 * T ≤ K) (hj : j ≤ 6 * T) (r : ℝ) :
    ‖iteratedDeriv j (maskedFrequencyCutoff K) r‖ ≤ (504 * (T : ℝ) ^ 2) ^ j := by
  have hfact : (j.factorial : ℝ) ≤ (6 * (T : ℝ)) ^ j := by
    have hf : j.factorial ≤ j ^ j := Nat.factorial_le_pow j
    have hj' : (j : ℝ) ≤ 6 * (T : ℝ) := by exact_mod_cast hj
    exact (by exact_mod_cast hf : (j.factorial : ℝ) ≤ (j : ℝ) ^ j).trans
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hj' j)
  calc
    _ ≤ (14 : ℝ) ^ j * (j.factorial : ℝ) ^ 2 :=
      norm_iteratedDeriv_maskedFrequencyCutoff_le K j (hj.trans hK) r
    _ ≤ (14 : ℝ) ^ j * ((6 * (T : ℝ)) ^ j) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hfact 2) (by positivity)
    _ = _ := by rw [← pow_mul, Nat.mul_comm j 2, pow_mul, ← mul_pow]; congr 1; ring

end FalconerThetaGauge
