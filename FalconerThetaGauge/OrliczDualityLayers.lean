module

public import FalconerThetaGauge.OrliczDuality
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Scalar logarithmic layer estimates

The weighted dyadic amplitude layers used in Lemma 5.3 grow like the γ-th
power of their count. The proof below counts an actual block of terms rather
than assuming a logarithmic tail estimate.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace FalconerThetaGauge

def dyadicAmplitudeLayerWeight (γ : ℝ) (j : ℕ) : ℝ := ((j : ℝ) + 1) ^ (γ - 1)

theorem dyadicAmplitudeLayerWeight_nonneg (γ : ℝ) (j : ℕ) :
    0 ≤ dyadicAmplitudeLayerWeight γ j := by unfold dyadicAmplitudeLayerWeight; positivity

theorem dyadic_layer_sum_lower (γ : ℝ) (hγ : 1 ≤ γ) (m : ℕ) :
    ((m : ℝ) + 1) ^ γ ≤ (4 : ℝ) ^ γ *
      (1 + ∑ j ∈ Finset.range m, dyadicAmplitudeLayerWeight γ j) := by
  have hγ₀ : 0 ≤ γ := zero_le_one.trans hγ
  have hsum : 0 ≤ ∑ j ∈ Finset.range m, dyadicAmplitudeLayerWeight γ j :=
    Finset.sum_nonneg fun j _ ↦ dyadicAmplitudeLayerWeight_nonneg γ j
  let k := m / 2
  by_cases hk : k = 0
  · have hm : m ≤ 1 := by dsimp [k] at hk; omega
    have hbase : (m : ℝ) + 1 ≤ 4 := by exact_mod_cast (show m + 1 ≤ 4 by omega)
    have hp := Real.rpow_le_rpow (by positivity) hbase hγ₀
    exact hp.trans (by nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) γ])
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hk)
  have hkm : 2 * k ≤ m := by dsimp [k]; omega
  have hm4k : (m : ℝ) + 1 ≤ 4 * (k : ℝ) := by
    exact_mod_cast (show m + 1 ≤ 4 * k by dsimp [k] at *; omega)
  have hblock : (k : ℝ) ^ γ ≤ ∑ j ∈ Finset.range k, dyadicAmplitudeLayerWeight γ (k + j) := by
    have hterm : ∀ j ∈ Finset.range k, (k : ℝ) ^ (γ - 1) ≤
        dyadicAmplitudeLayerWeight γ (k + j) := by
      intro j _
      unfold dyadicAmplitudeLayerWeight
      apply Real.rpow_le_rpow hkpos.le _ (by linarith)
      push_cast
      linarith [show 0 ≤ (j : ℝ) by positivity]
    have h := Finset.sum_le_sum hterm
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    have hid : (k : ℝ) * (k : ℝ) ^ (γ - 1) = (k : ℝ) ^ γ := by
      conv_lhs => lhs; rw [← Real.rpow_one (k : ℝ)]
      rw [← Real.rpow_add hkpos]
      congr 1
      ring
    rwa [hid] at h
  have hprefix : (∑ j ∈ Finset.range k, dyadicAmplitudeLayerWeight γ (k + j)) ≤
      ∑ j ∈ Finset.range (2 * k), dyadicAmplitudeLayerWeight γ j := by
    rw [show 2 * k = k + k by omega, Finset.sum_range_add]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun j _ ↦ dyadicAmplitudeLayerWeight_nonneg γ j)
  have hprefix' : (∑ j ∈ Finset.range (2 * k), dyadicAmplitudeLayerWeight γ j) ≤
      ∑ j ∈ Finset.range m, dyadicAmplitudeLayerWeight γ j := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkm)
      (fun j _ _ ↦ dyadicAmplitudeLayerWeight_nonneg γ j)
  calc
    ((m : ℝ) + 1) ^ γ ≤ (4 * (k : ℝ)) ^ γ := Real.rpow_le_rpow (by positivity) hm4k hγ₀
    _ = (4 : ℝ) ^ γ * (k : ℝ) ^ γ := Real.mul_rpow (by norm_num) hkpos.le
    _ ≤ (4 : ℝ) ^ γ * (∑ j ∈ Finset.range m, dyadicAmplitudeLayerWeight γ j) :=
      mul_le_mul_of_nonneg_left (hblock.trans (hprefix.trans hprefix')) (by positivity)
    _ ≤ _ := by nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) γ]

def dyadicAmplitudeLayer (γ B t : ℝ) (j : ℕ) : ℝ≥0∞ :=
  if B * (2 : ℝ) ^ j < t then ENNReal.ofReal (dyadicAmplitudeLayerWeight γ j) else 0

def amplitudeLogConstant (B : ℝ) : ℝ := Real.log (Real.exp 1 + B) + Real.log 2

theorem amplitudeLogConstant_pos {B : ℝ} (hB : 0 < B) : 0 < amplitudeLogConstant B := by
  unfold amplitudeLogConstant
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  exact add_pos (Real.log_pos (by linarith)) (Real.log_pos (by norm_num))

theorem logarithmic_amplitude_layer_le (γ B t : ℝ) (hγ : 1 ≤ γ) (hB : 0 < B) (ht : 0 ≤ t) :
    ENNReal.ofReal ((Real.log (Real.exp 1 + t)) ^ γ) ≤
      ENNReal.ofReal ((4 * amplitudeLogConstant B) ^ γ) *
        (1 + ∑' j, dyadicAmplitudeLayer γ B t j) := by
  have hγ₀ : 0 ≤ γ := zero_le_one.trans hγ
  have hD := amplitudeLogConstant_pos hB
  have hC : 0 ≤ (4 * amplitudeLogConstant B) ^ γ := by positivity
  have hlog : 0 ≤ Real.log (Real.exp 1 + t) :=
    zero_le_one.trans (log_exp_one_add_ge_one ht)
  by_cases htB : t < B
  · have hl : Real.log (Real.exp 1 + t) ≤ 4 * amplitudeLogConstant B := by
      have h := Real.log_le_log (by positivity : 0 < Real.exp 1 + t) (by linarith :
        Real.exp 1 + t ≤ Real.exp 1 + B)
      unfold amplitudeLogConstant at *
      linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    have hp := ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hlog hl hγ₀)
    exact hp.trans (by
      conv_lhs => rw [← mul_one (ENNReal.ofReal ((4 * amplitudeLogConstant B) ^ γ))]
      exact mul_le_mul' le_rfl (le_add_of_nonneg_right (by positivity)))
  obtain ⟨m, hmlo, hmhi⟩ := exists_nat_pow_near
    ((one_le_div₀ hB).mpr (le_of_not_gt htB)) (by norm_num : (1 : ℝ) < 2)
  have hpow : 1 ≤ (2 : ℝ) ^ (m + 1) := one_le_pow₀ (by norm_num)
  have htupper : t < B * (2 : ℝ) ^ (m + 1) := by
    have h := (div_lt_iff₀ hB).mp hmhi
    simpa only [mul_comm] using h
  have hl : Real.log (Real.exp 1 + t) ≤ amplitudeLogConstant B * ((m : ℝ) + 1) := by
    have harg : Real.exp 1 + t ≤ (Real.exp 1 + B) * (2 : ℝ) ^ (m + 1) := by
      have h := mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg 1)
      nlinarith
    have h := Real.log_le_log (by positivity : 0 < Real.exp 1 + t) harg
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h
    push_cast at h
    have hpositive : 0 ≤ Real.log (Real.exp 1 + B) :=
      zero_le_one.trans (log_exp_one_add_ge_one hB.le)
    unfold amplitudeLogConstant
    nlinarith [mul_nonneg hpositive (show 0 ≤ (m : ℝ) by positivity)]
  have hp : (Real.log (Real.exp 1 + t)) ^ γ ≤
      (4 * amplitudeLogConstant B) ^ γ *
        (1 + ∑ j ∈ Finset.range m, dyadicAmplitudeLayerWeight γ j) := by
    calc
      _ ≤ (amplitudeLogConstant B * ((m : ℝ) + 1)) ^ γ := Real.rpow_le_rpow hlog hl hγ₀
      _ = (amplitudeLogConstant B) ^ γ * ((m : ℝ) + 1) ^ γ :=
        Real.mul_rpow hD.le (by positivity)
      _ ≤ (amplitudeLogConstant B) ^ γ * ((4 : ℝ) ^ γ *
          (1 + ∑ j ∈ Finset.range m, dyadicAmplitudeLayerWeight γ j)) :=
        mul_le_mul_of_nonneg_left (dyadic_layer_sum_lower γ hγ m) (by positivity)
      _ = _ := by rw [Real.mul_rpow (by norm_num) hD.le]; ring
  have hactive : ∀ j ∈ Finset.range m, B * (2 : ℝ) ^ j < t := by
    intro j hj
    have hpowlt : (2 : ℝ) ^ j < (2 : ℝ) ^ m :=
      pow_lt_pow_right₀ (by norm_num) (Finset.mem_range.mp hj)
    have hlo : B * (2 : ℝ) ^ m ≤ t := by
      simpa only [mul_comm] using (le_div_iff₀ hB).mp hmlo
    exact (mul_lt_mul_of_pos_left hpowlt hB).trans_le hlo
  have hsum : ENNReal.ofReal (∑ j ∈ Finset.range m, dyadicAmplitudeLayerWeight γ j) ≤
      ∑' j, dyadicAmplitudeLayer γ B t j := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ dyadicAmplitudeLayerWeight_nonneg γ j)]
    calc
      _ = ∑ j ∈ Finset.range m, dyadicAmplitudeLayer γ B t j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [dyadicAmplitudeLayer, ite_eq_left (hactive j hj)]
      _ ≤ _ := ENNReal.sum_le_tsum (Finset.range m)
  calc
    _ ≤ ENNReal.ofReal ((4 * amplitudeLogConstant B) ^ γ *
        (1 + ∑ j ∈ Finset.range m, dyadicAmplitudeLayerWeight γ j)) := ENNReal.ofReal_le_ofReal hp
    _ = ENNReal.ofReal ((4 * amplitudeLogConstant B) ^ γ) *
        (1 + ENNReal.ofReal (∑ j ∈ Finset.range m, dyadicAmplitudeLayerWeight γ j)) := by
      rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_add (by norm_num)
        (Finset.sum_nonneg fun j _ ↦ dyadicAmplitudeLayerWeight_nonneg γ j), ENNReal.ofReal_one]
    _ ≤ _ := mul_le_mul' le_rfl (add_le_add le_rfl hsum)

def frequencyLayerLogConstant : ℝ := 1 + (Real.log 2)⁻¹

theorem dyadic_frequency_layer_le (γ t : ℝ) (hγ : 1 ≤ γ) (ht : 0 ≤ t) :
    (∑' j, dyadicAmplitudeLayer γ 1 t j) ≤
      ENNReal.ofReal (frequencyLayerLogConstant ^ γ) *
        ENNReal.ofReal ((Real.log (Real.exp 1 + t)) ^ γ) := by
  have hγ₀ : 0 ≤ γ := zero_le_one.trans hγ
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < frequencyLayerLogConstant := by unfold frequencyLayerLogConstant; positivity
  by_cases ht₁ : t < 1
  · have hz : ∀ j, dyadicAmplitudeLayer γ 1 t j = 0 := by
      intro j
      unfold dyadicAmplitudeLayer
      rw [one_mul, ite_eq_right]
      exact not_lt.mpr (ht₁.le.trans (one_le_pow₀ (by norm_num)))
    simp_rw [hz, tsum_zero]
    exact zero_le
  obtain ⟨m, hmlo, hmhi⟩ := exists_nat_pow_near (le_of_not_gt ht₁) (by norm_num : (1 : ℝ) < 2)
  have hzero : ∀ j ∉ Finset.range (m + 1), dyadicAmplitudeLayer γ 1 t j = 0 := by
    intro j hj
    have hjm : m + 1 ≤ j := by simpa only [Finset.mem_range, not_lt] using hj
    have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hjm
    unfold dyadicAmplitudeLayer
    rw [one_mul, ite_eq_right (not_lt.mpr (hmhi.le.trans hpow))]
  rw [tsum_eq_sum hzero]
  have hs : (∑ j ∈ Finset.range (m + 1), dyadicAmplitudeLayerWeight γ j) ≤
      ((m : ℝ) + 1) ^ γ := by
    have hterm : ∀ j ∈ Finset.range (m + 1), dyadicAmplitudeLayerWeight γ j ≤
        ((m : ℝ) + 1) ^ (γ - 1) := by
      intro j hj
      unfold dyadicAmplitudeLayerWeight
      apply Real.rpow_le_rpow (by positivity) _ (by linarith)
      have hj' := Finset.mem_range.mp hj
      exact_mod_cast (show j + 1 ≤ m + 1 by omega)
    have h := Finset.sum_le_sum hterm
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at h
    have hid : ((m : ℝ) + 1) * ((m : ℝ) + 1) ^ (γ - 1) = ((m : ℝ) + 1) ^ γ := by
      conv_lhs => lhs; rw [← Real.rpow_one ((m : ℝ) + 1)]
      rw [← Real.rpow_add (by positivity)]
      congr 1
      ring
    rwa [hid] at h
  have hc : (m : ℝ) + 1 ≤ frequencyLayerLogConstant * Real.log (Real.exp 1 + t) := by
    have hl := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ m) hmlo
    rw [Real.log_pow] at hl
    have hl' := Real.log_le_log (by linarith : 0 < t)
      (show t ≤ Real.exp 1 + t by linarith [Real.exp_pos 1])
    have hdiv : (m : ℝ) ≤ Real.log (Real.exp 1 + t) / Real.log 2 :=
      (le_div_iff₀ hlog₂).mpr (hl.trans hl')
    have hlog := log_exp_one_add_ge_one ht
    unfold frequencyLayerLogConstant
    rw [add_mul, one_mul, ← div_eq_inv_mul]
    linarith
  have hp : ((m : ℝ) + 1) ^ γ ≤ frequencyLayerLogConstant ^ γ *
      (Real.log (Real.exp 1 + t)) ^ γ := by
    rw [← Real.mul_rpow hD.le (zero_le_one.trans (log_exp_one_add_ge_one ht))]
    exact Real.rpow_le_rpow (by positivity) hc hγ₀
  calc
    _ ≤ ∑ j ∈ Finset.range (m + 1), ENNReal.ofReal (dyadicAmplitudeLayerWeight γ j) := by
      apply Finset.sum_le_sum
      intro j _
      unfold dyadicAmplitudeLayer
      split_ifs <;> simp
    _ = ENNReal.ofReal (∑ j ∈ Finset.range (m + 1), dyadicAmplitudeLayerWeight γ j) :=
      (ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ dyadicAmplitudeLayerWeight_nonneg γ j)).symm
    _ ≤ ENNReal.ofReal (frequencyLayerLogConstant ^ γ * (Real.log (Real.exp 1 + t)) ^ γ) :=
      ENNReal.ofReal_le_ofReal (hs.trans hp)
    _ = _ := ENNReal.ofReal_mul (by positivity)

end FalconerThetaGauge
