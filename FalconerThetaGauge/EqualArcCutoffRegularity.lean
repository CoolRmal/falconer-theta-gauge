module

public import FalconerThetaGauge.EqualArcCutoff

/-! # Angular cutoff regularity independent of the larger chosen bump order -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped ContDiff

namespace FalconerThetaGauge

theorem norm_iteratedDeriv_equalArcCutoff_le_of_order {T K : ℕ} (hK : 6 * T ≤ K) {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hℓ₁ : ℓ ≤ 1) (i : Fin (angularPartitionCount ℓ))
    {k : ℕ} (hk : k ≤ 6 * T) (θ : ℝ) :
    ‖iteratedDeriv k (fun θ ↦
      equalArcCutoff K ℓ i (unitCircleOfAngle θ)) θ‖ ≤
      (576 * (T : ℝ) ^ 2 / ℓ) ^ k := by
  unfold equalArcCutoff
  simp_rw [equalAngularPartition_comp_angle]
  let w := equalAngularCellWidth (angularPartitionCount ℓ)
  have hw : 0 < w := by
    have hh := equalArcCutoff_scale_pos hℓ
    dsimp [w]
    linarith
  have hlo : ℓ / 2 ≤ w := equalAngularCellWidth_lower hℓ hℓ₁
  have hpi : Real.pi ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_pos, Real.pi_lt_d4]
  calc
    _ ≤ (w / 4)⁻¹ ^ k * ((Real.pi ^ 2 / 6) ^ k * (k.factorial : ℝ) ^ 2) :=
      norm_iteratedDeriv_smoothIndicator_le_explicit K k (hk.trans hK) (by positivity)
        (measurableSet_equalAngularCell _ i) θ
    _ ≤ (w / 4)⁻¹ ^ k * (2 ^ k * ((6 * (T : ℝ)) ^ k) ^ 2) := by
      gcongr
      exact factorial_cast_le_cutoff_order_pow hk
    _ = ((w / 4)⁻¹ * (2 * (6 * (T : ℝ)) ^ 2)) ^ k := by
      have hp : ((6 * (T : ℝ)) ^ k) ^ 2 = ((6 * (T : ℝ)) ^ 2) ^ k := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2]
      rw [hp, ← mul_pow, ← mul_pow]
    _ ≤ _ := by
      apply pow_le_pow_left₀ (by positivity)
      have he : (w / 4)⁻¹ * (2 * (6 * (T : ℝ)) ^ 2) =
          288 * (T : ℝ) ^ 2 / w := by field_simp; ring
      rw [he]
      apply (div_le_div_iff₀ hw hℓ).mpr
      nlinarith [sq_nonneg (T : ℝ), mul_nonneg
        (sq_nonneg (T : ℝ)) (sub_nonneg.mpr hlo)]

theorem equalArcCutoff_isDerivativeRegular_of_order {T K : ℕ}
    (hT : 1 ≤ T) (hK : 6 * T ≤ K)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ₁ : ℓ ≤ 1) (i : Fin (angularPartitionCount ℓ)) :
    IsDerivativeRegular 1 (576 * (T : ℝ) ^ 2 / ℓ) (6 * T)
      (fun θ ↦ (equalArcCutoff K ℓ i (unitCircleOfAngle θ) : ℂ)) := by
  have hf := contDiff_equalArcCutoff_comp_angle K hℓ i
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hscale : 1 ≤ 576 * (T : ℝ) ^ 2 / ℓ := by
    apply (le_div_iff₀ hℓ).mpr
    nlinarith
  refine ⟨by norm_num, hscale, (Complex.ofRealCLM.contDiff.comp hf).of_le
    (ENat.natCast_le_of_coe_top_le_withTop (le_refl ∞) (6 * T)), ?_⟩
  intro k hk θ
  rw [iteratedDeriv_ofReal_eq ((hf.of_le (by simp)).contDiffAt)]
  simpa only [Complex.norm_real, Real.norm_eq_abs, one_mul] using
    norm_iteratedDeriv_equalArcCutoff_le_of_order hK hℓ hℓ₁ i hk θ


end FalconerThetaGauge
