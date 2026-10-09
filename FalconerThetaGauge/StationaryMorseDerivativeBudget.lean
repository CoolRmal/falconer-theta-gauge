module

public import FalconerThetaGauge.StationaryGevreyProduct
public import FalconerThetaGauge.CircularStationaryCutoff
public import FalconerThetaGauge.StationaryMorseAmplitude

/-! # Uniform derivatives of the literal localized circular amplitude -/

@[expose] public section

noncomputable section

open Set
open scoped ContDiff

namespace FalconerThetaGauge

theorem iteratedDeriv_ofReal_function {f : ℝ → ℝ} {n : ℕ} {x : ℝ}
    (hf : ContDiffAt ℝ n f x) :
    iteratedDeriv n (fun s ↦ (f s : ℂ)) x = ((iteratedDeriv n f x : ℝ) : ℂ) := by
  simpa only [Complex.real_smul, mul_one] using iteratedDeriv_smul_const hf (1 : ℂ)

theorem norm_iteratedDeriv_circularCutoff_morse_le {K k : ℕ} (hk : k ≤ K)
    {s : ℝ} (hs : |s| ≤ 1) :
    ‖iteratedDeriv k
      (fun t ↦ (circularStationaryCutoff K (stationaryMorseAngle t) : ℂ)) s‖ ≤
        48 ^ k * (k.factorial : ℝ) ^ 2 := by
  have hi : s ∈ Ioo (-2 : ℝ) 2 := by
    rcases abs_le.mp hs with ⟨hlo, hhi⟩
    constructor <;> linarith
  have hθ : ContDiffAt ℝ k stationaryMorseAngle s :=
    (contDiffAt_stationaryMorseAngle hi).of_le (by simp)
  have hχ : ContDiffAt ℝ k (fun t ↦ (circularStationaryCutoff K t : ℂ))
      (stationaryMorseAngle s) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _
      ((contDiff_circularStationaryCutoff K).contDiffAt.of_le (by simp))
  have h := norm_iteratedDeriv_comp_le_gevrey hθ hχ
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 8)
    (by norm_num : (0 : ℝ) ≤ 2)
    (fun m hm _ ↦ norm_iteratedDeriv_stationaryMorseAngle_le m hm hs) (by
      intro j hj
      rw [iteratedDeriv_ofReal_function
        ((contDiff_circularStationaryCutoff K).contDiffAt.of_le (by simp)),
        Complex.norm_real]
      have hh := norm_iteratedDeriv_circularStationaryCutoff_le K j (hj.trans hk)
        (stationaryMorseAngle s)
      have hscale : 2 * Real.pi ≤ (8 : ℝ) := by linarith [Real.pi_le_four]
      exact hh.trans (by simp only [one_mul]; gcongr))
  simpa only [Function.comp_def, one_mul, show (3 * 8 * 2 : ℝ) = 48 by norm_num] using h

theorem norm_iteratedDeriv_regular_morse_le {K k : ℕ} (hk : k ≤ K)
    {G : ℝ → ℂ} {A M φ s : ℝ} (hG : IsDerivativeRegular A M K G) (hs : |s| ≤ 1) :
    ‖iteratedDeriv k (fun t ↦ G (φ + stationaryMorseAngle t)) s‖ ≤
      A * (6 * M) ^ k * (k.factorial : ℝ) ^ 2 := by
  have hi : s ∈ Ioo (-2 : ℝ) 2 := by
    rcases abs_le.mp hs with ⟨hlo, hhi⟩
    constructor <;> linarith
  have hθ : ContDiffAt ℝ k (fun t ↦ φ + stationaryMorseAngle t) s :=
    contDiffAt_const.add ((contDiffAt_stationaryMorseAngle hi).of_le (by simp))
  have h := norm_iteratedDeriv_comp_le_gevrey hθ
    ((hG.smooth.of_le (by exact_mod_cast hk)).contDiffAt)
    hG.amplitude_nonneg hG.one_le_scale (by norm_num : (0 : ℝ) ≤ 2) (by
      intro j hj _
      rw [iteratedDeriv_const_add hj]
      exact norm_iteratedDeriv_stationaryMorseAngle_le j hj hs) (by
      intro j hj
      have hh := hG.bound j (hj.trans hk) (φ + stationaryMorseAngle s)
      have hf : (1 : ℝ) ≤ (j.factorial : ℝ) := by
        exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos j)
      have hf2 : (1 : ℝ) ≤ (j.factorial : ℝ) ^ 2 := by nlinarith
      have ha : 0 ≤ A * M ^ j :=
        mul_nonneg hG.amplitude_nonneg (pow_nonneg (by linarith [hG.one_le_scale]) j)
      exact hh.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hf2 ha))
  simpa only [Function.comp_def, show (3 * M * 2 : ℝ) = 6 * M by ring] using h

theorem norm_iteratedDeriv_complex_stationaryMorseJacobian_le (k : ℕ) {s : ℝ}
    (hs : |s| ≤ 1) :
    ‖iteratedDeriv k (fun t ↦ (stationaryMorseJacobian t : ℂ)) s‖ ≤
      2 * 2 ^ k * (k.factorial : ℝ) ^ 2 := by
  have hi : s ∈ Ioo (-2 : ℝ) 2 := by
    rcases abs_le.mp hs with ⟨hlo, hhi⟩
    constructor <;> linarith
  rw [iteratedDeriv_ofReal_function
    ((contDiffAt_stationaryMorseJacobian hi).of_le (by simp)), Complex.norm_real]
  have hf : (1 : ℝ) ≤ (k.factorial : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos k)
  have hfac : (k.factorial : ℝ) ≤ (k.factorial : ℝ) ^ 2 := by nlinarith
  calc
    _ ≤ 2 * (k.factorial : ℝ) * 2 ^ k :=
      norm_iteratedDeriv_stationaryMorseJacobian_le k hs
    _ = 2 * 2 ^ k * (k.factorial : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hfac (by positivity)

/-- The actual localized amplitude has a uniform finite Gevrey budget on its whole support. -/
theorem norm_iteratedDeriv_stationaryMorseAmplitude_le {K k : ℕ} (hk : k ≤ K)
    {G : ℝ → ℂ} {A M φ s : ℝ} (hG : IsDerivativeRegular A M K G) (hs : |s| ≤ 1) :
    ‖iteratedDeriv k (stationaryMorseAmplitude (circularStationaryCutoff K) G φ) s‖ ≤
      2 * A * (56 * M) ^ k * (k.factorial : ℝ) ^ 2 := by
  have hi : s ∈ Ioo (-2 : ℝ) 2 := by
    rcases abs_le.mp hs with ⟨hlo, hhi⟩
    constructor <;> linarith
  have hθ : ContDiffAt ℝ k stationaryMorseAngle s :=
    (contDiffAt_stationaryMorseAngle hi).of_le (by simp)
  have hχ : ContDiffAt ℝ k
      (fun t ↦ (circularStationaryCutoff K (stationaryMorseAngle t) : ℂ)) s :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp s
      (((contDiff_circularStationaryCutoff K).contDiffAt.of_le (by simp)).comp s hθ)
  have hGc : ContDiffAt ℝ k (fun t ↦ G (φ + stationaryMorseAngle t)) s :=
    ((hG.smooth.of_le (by exact_mod_cast hk)).contDiffAt).comp s (contDiffAt_const.add hθ)
  have hJ : ContDiffAt ℝ k (fun t ↦ (stationaryMorseJacobian t : ℂ)) s :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp s
      ((contDiffAt_stationaryMorseJacobian hi).of_le (by simp))
  have hCG (j : ℕ) (hj : j ≤ k) := norm_iteratedDeriv_mul_le_gevrey
    (hχ.of_le (by exact_mod_cast hj)) (hGc.of_le (by exact_mod_cast hj))
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 48)
    hG.amplitude_nonneg (by linarith [hG.one_le_scale] : 0 ≤ 6 * M)
    (fun m hm ↦ by simpa only [one_mul] using
      norm_iteratedDeriv_circularCutoff_morse_le ((hm.trans hj).trans hk) hs)
    (fun m hm ↦ norm_iteratedDeriv_regular_morse_le ((hm.trans hj).trans hk) hG hs)
  have h := norm_iteratedDeriv_mul_le_gevrey (hχ.mul hGc) hJ
    hG.amplitude_nonneg (by linarith [hG.one_le_scale] : 0 ≤ 48 + 6 * M)
    (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 2)
    (fun j hj ↦ by
      have hb := hCG j hj
      change ‖iteratedDeriv j
        (fun t ↦ (circularStationaryCutoff K (stationaryMorseAngle t) : ℂ) *
          G (φ + stationaryMorseAngle t)) s‖ ≤ _ at hb
      simpa only [one_mul] using hb)
    (fun j _ ↦ norm_iteratedDeriv_complex_stationaryMorseJacobian_le j hs)
  change ‖iteratedDeriv k (stationaryMorseAmplitude (circularStationaryCutoff K) G φ) s‖ ≤
    _ at h
  calc
    _ ≤ (A * 2) * (48 + 6 * M + 2) ^ k * (k.factorial : ℝ) ^ 2 := h
    _ = (2 * A) * (48 + 6 * M + 2) ^ k * (k.factorial : ℝ) ^ 2 := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hG.amplitude_nonneg)
      exact pow_le_pow_left₀ (by linarith [hG.one_le_scale])
        (by linarith [hG.one_le_scale]) k

end FalconerThetaGauge
