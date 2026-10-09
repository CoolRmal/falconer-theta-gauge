module

public import FalconerThetaGauge.OrliczEnergyFourierSeries

/-!
# The logarithmic Fourier weight above unit frequency

A single Gaussian in the dyadic series dominates the singular logarithmic
Fourier weight at each frequency of norm at least one. The chosen index is
obtained from the Archimedean dyadic cutoff theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace FalconerThetaGauge

def dyadicFrequencyGaussianTerm (γ r : ℝ) (n : ℕ) : ℝ :=
  (((n : ℝ) + 1) ^ γ / (2 : ℝ) ^ n) * Real.exp (-(r ^ 2 / (4 : ℝ) ^ (n + 1)))

def logarithmicFourierComparisonConstant (γ : ℝ) : ℝ :=
  Real.exp 1 * (Real.log (Real.exp 1 + 1) + Real.log 2) ^ γ

theorem logarithmicFourierComparisonConstant_pos (γ : ℝ) :
    0 < logarithmicFourierComparisonConstant γ := by
  unfold logarithmicFourierComparisonConstant
  apply mul_pos (Real.exp_pos _)
  apply Real.rpow_pos_of_pos
  have hlog : 0 < Real.log (Real.exp 1 + 1) :=
    Real.log_pos (by linarith [Real.exp_pos 1])
  exact add_pos hlog (Real.log_pos (by norm_num))

theorem exists_frequencyGaussian_domination (γ r : ℝ) (hγ : 0 ≤ γ) (hr : 1 ≤ r) :
    ∃ n : ℕ, (Real.log (Real.exp 1 + r)) ^ γ / r ≤
      logarithmicFourierComparisonConstant γ * dyadicFrequencyGaussianTerm γ r n := by
  obtain ⟨n, hnlow, hnhigh⟩ := exists_nat_pow_near hr (by norm_num : (1 : ℝ) < 2)
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hn : 1 ≤ (2 : ℝ) ^ (n + 1) := one_le_pow₀ (by norm_num)
  have he : 0 < Real.exp 1 + 1 := by positivity
  let D := Real.log (Real.exp 1 + 1) + Real.log 2
  have hD : 0 < D := by
    dsimp [D]
    exact add_pos (Real.log_pos (by linarith [Real.exp_pos 1]))
      (Real.log_pos (by norm_num))
  have hlog : Real.log (Real.exp 1 + r) ≤ D * ((n : ℝ) + 1) := by
    have hmul : Real.exp 1 + r ≤ (Real.exp 1 + 1) * (2 : ℝ) ^ (n + 1) := by
      have h := mul_le_mul_of_nonneg_left hn (Real.exp_nonneg 1)
      nlinarith [hnhigh.le]
    have hmono := Real.log_le_log (by positivity : 0 < Real.exp 1 + r) hmul
    rw [Real.log_mul he.ne' (by positivity), Real.log_pow] at hmono
    push_cast at hmono
    have hlogpos : 0 ≤ Real.log (Real.exp 1 + 1) := (Real.log_pos (by
      linarith [Real.exp_pos 1])).le
    dsimp [D]
    nlinarith [mul_nonneg hlogpos (show 0 ≤ (n : ℝ) by positivity)]
  have hlognonneg : 0 ≤ Real.log (Real.exp 1 + r) :=
    Real.log_nonneg (by linarith [Real.exp_pos 1])
  have hpow : (Real.log (Real.exp 1 + r)) ^ γ ≤ D ^ γ * ((n : ℝ) + 1) ^ γ := by
    rw [← Real.mul_rpow hD.le (by positivity)]
    exact Real.rpow_le_rpow hlognonneg hlog hγ
  have hweight : (Real.log (Real.exp 1 + r)) ^ γ / r ≤
      D ^ γ * (((n : ℝ) + 1) ^ γ / (2 : ℝ) ^ n) := by
    rw [← mul_div_assoc]
    exact div_le_div₀ (by positivity) hpow (by positivity) hnlow
  have hfour : (4 : ℝ) ^ (n + 1) = ((2 : ℝ) ^ (n + 1)) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm (n + 1) 2, pow_mul]
    norm_num
  have hratio : r ^ 2 / (4 : ℝ) ^ (n + 1) ≤ 1 := by
    rw [div_le_one₀ (by positivity), hfour]
    exact (sq_le_sq₀ hrpos.le (by positivity)).mpr hnhigh.le
  have hgaussian : 1 ≤ Real.exp 1 * Real.exp (-(r ^ 2 / (4 : ℝ) ^ (n + 1))) := by
    rw [← Real.exp_add, Real.one_le_exp_iff]
    linarith
  refine ⟨n, hweight.trans ?_⟩
  have hm := mul_le_mul_of_nonneg_left hgaussian
    (show 0 ≤ D ^ γ * (((n : ℝ) + 1) ^ γ / (2 : ℝ) ^ n) by positivity)
  simpa only [mul_one, one_mul, logarithmicFourierComparisonConstant, dyadicFrequencyGaussianTerm,
    D, mul_assoc, mul_left_comm, mul_comm] using hm

/-- The literal singular Fourier weight; its value at the origin is infinite. -/
def logarithmicFourierWeight (γ : ℝ) (ξ : Plane) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.log (Real.exp 1 + ‖ξ‖)) ^ γ) * (ENNReal.ofReal ‖ξ‖)⁻¹

/-- The manuscript's logarithmically weighted Fourier energy. -/
def logarithmicFourierEnergy (γ : ℝ) (μ : Measure Plane) : ℝ≥0∞ :=
  ∫⁻ ξ : Plane, ENNReal.ofReal (‖planarMeasureFourier μ ξ‖ ^ 2) *
    logarithmicFourierWeight γ ξ

theorem logarithmicFourierWeight_le (γ : ℝ) (hγ : 0 ≤ γ) (ξ : Plane)
    (hξ : 1 ≤ ‖ξ‖) :
    logarithmicFourierWeight γ ξ ≤ ENNReal.ofReal (logarithmicFourierComparisonConstant γ) *
      ∑' n, ENNReal.ofReal (dyadicFrequencyGaussianTerm γ ‖ξ‖ n) := by
  obtain ⟨n, hn⟩ := exists_frequencyGaussian_domination γ ‖ξ‖ hγ hξ
  have hpos : 0 < ‖ξ‖ := lt_of_lt_of_le zero_lt_one hξ
  calc
    logarithmicFourierWeight γ ξ =
        ENNReal.ofReal ((Real.log (Real.exp 1 + ‖ξ‖)) ^ γ / ‖ξ‖) := by
      rw [logarithmicFourierWeight, ← div_eq_mul_inv, ENNReal.ofReal_div_of_pos hpos]
    _ ≤ ENNReal.ofReal (logarithmicFourierComparisonConstant γ *
        dyadicFrequencyGaussianTerm γ ‖ξ‖ n) := ENNReal.ofReal_le_ofReal hn
    _ = ENNReal.ofReal (logarithmicFourierComparisonConstant γ) *
        ENNReal.ofReal (dyadicFrequencyGaussianTerm γ ‖ξ‖ n) :=
      ENNReal.ofReal_mul (logarithmicFourierComparisonConstant_pos γ).le
    _ ≤ ENNReal.ofReal (logarithmicFourierComparisonConstant γ) *
        ∑' n, ENNReal.ofReal (dyadicFrequencyGaussianTerm γ ‖ξ‖ n) :=
      mul_le_mul' le_rfl (ENNReal.le_tsum (f := fun n ↦
        ENNReal.ofReal (dyadicFrequencyGaussianTerm γ ‖ξ‖ n)) n)

theorem lintegral_fourier_high_le_series (γ : ℝ) (hγ : 0 ≤ γ) (μ : Measure Plane)
    [IsProbabilityMeasure μ] :
    ∫⁻ ξ : Plane in {ξ | 1 ≤ ‖ξ‖}, ENNReal.ofReal (‖planarMeasureFourier μ ξ‖ ^ 2) *
        logarithmicFourierWeight γ ξ ≤
      ENNReal.ofReal (logarithmicFourierComparisonConstant γ) *
        ∑' n, dyadicGaussianFourierTerm γ μ n := by
  have hs : MeasurableSet {ξ : Plane | 1 ≤ ‖ξ‖} := by measurability
  calc
    _ ≤ ∫⁻ ξ : Plane in {ξ | 1 ≤ ‖ξ‖},
        ENNReal.ofReal (logarithmicFourierComparisonConstant γ) *
          (ENNReal.ofReal (‖planarMeasureFourier μ ξ‖ ^ 2) *
            ∑' n, ENNReal.ofReal (dyadicFrequencyGaussianTerm γ ‖ξ‖ n)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hs] with ξ hξ
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul' (show ENNReal.ofReal (‖planarMeasureFourier μ ξ‖ ^ 2) ≤
          ENNReal.ofReal (‖planarMeasureFourier μ ξ‖ ^ 2) from le_rfl)
          (logarithmicFourierWeight_le γ hγ ξ hξ)
    _ ≤ ∫⁻ ξ : Plane, ENNReal.ofReal (logarithmicFourierComparisonConstant γ) *
          (ENNReal.ofReal (‖planarMeasureFourier μ ξ‖ ^ 2) *
            ∑' n, ENNReal.ofReal (dyadicFrequencyGaussianTerm γ ‖ξ‖ n)) :=
      setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (logarithmicFourierComparisonConstant γ) *
        ∑' n, dyadicGaussianFourierTerm γ μ n := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have he (ξ : Plane) : ENNReal.ofReal (‖planarMeasureFourier μ ξ‖ ^ 2) *
          ∑' n, ENNReal.ofReal (dyadicFrequencyGaussianTerm γ ‖ξ‖ n) =
          ∑' n, ENNReal.ofReal (‖planarMeasureFourier μ ξ‖ ^ 2) *
            ENNReal.ofReal (dyadicFrequencyGaussianTerm γ ‖ξ‖ n) :=
        ENNReal.tsum_mul_left.symm
      simp_rw [he]
      rw [lintegral_tsum (fun n ↦ by unfold dyadicFrequencyGaussianTerm; fun_prop)]
      congr 1
      apply tsum_congr
      intro n
      simp_rw [dyadicFrequencyGaussianTerm, ENNReal.ofReal_mul (by positivity :
        0 ≤ ((n : ℝ) + 1) ^ γ / (2 : ℝ) ^ n)]
      simp_rw [mul_left_comm (ENNReal.ofReal (‖planarMeasureFourier μ _‖ ^ 2))]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      unfold dyadicGaussianFourierTerm
      simp_rw [mul_comm (ENNReal.ofReal (‖planarMeasureFourier μ _‖ ^ 2))]
      simp_rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]

theorem lintegral_fourier_high_le (γ : ℝ) (hγ : 0 ≤ γ) (μ : Measure Plane)
    [IsProbabilityMeasure μ] :
    ∫⁻ ξ : Plane in {ξ | 1 ≤ ‖ξ‖}, ENNReal.ofReal (‖planarMeasureFourier μ ξ‖ ^ 2) *
        logarithmicFourierWeight γ ξ ≤
      ENNReal.ofReal (logarithmicFourierComparisonConstant γ *
        (4 * Real.pi * dyadicGaussianEnergyConstant γ)) * (1 + logCriticalEnergy γ μ) := by
  refine (lintegral_fourier_high_le_series γ hγ μ).trans ?_
  rw [ENNReal.ofReal_mul (logarithmicFourierComparisonConstant_pos γ).le, mul_assoc]
  exact mul_le_mul' le_rfl (tsum_dyadicGaussianFourierTerm_le γ hγ μ)

theorem lintegral_fourier_low_le_inverse_norm (γ : ℝ) (hγ : 0 ≤ γ)
    (μ : Measure Plane) [IsProbabilityMeasure μ] :
    ∫⁻ ξ : Plane in Metric.ball 0 1, ENNReal.ofReal (‖planarMeasureFourier μ ξ‖ ^ 2) *
        logarithmicFourierWeight γ ξ ≤
      ENNReal.ofReal ((Real.log (Real.exp 1 + 1)) ^ γ) *
        ∫⁻ ξ : Plane in Metric.ball 0 1, (ENNReal.ofReal ‖ξ‖)⁻¹ := by
  calc
    _ ≤ ∫⁻ ξ : Plane in Metric.ball 0 1,
        ENNReal.ofReal ((Real.log (Real.exp 1 + 1)) ^ γ) * (ENNReal.ofReal ‖ξ‖)⁻¹ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with ξ hξ
      have hξnorm : ‖ξ‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hξ
      have hn : ENNReal.ofReal (‖planarMeasureFourier μ ξ‖ ^ 2) ≤ 1 := by
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        rw [norm_planarMeasureFourier]
        nlinarith [norm_charFun_le_one (μ := μ) ξ, norm_nonneg (charFun μ ξ)]
      have hl : ENNReal.ofReal ((Real.log (Real.exp 1 + ‖ξ‖)) ^ γ) ≤
          ENNReal.ofReal ((Real.log (Real.exp 1 + 1)) ^ γ) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.rpow_le_rpow _ _ hγ
        · apply Real.log_nonneg
          have he := (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1))
          linarith [norm_nonneg ξ]
        · exact Real.log_le_log (by positivity) (by linarith)
      calc
        _ ≤ 1 * (ENNReal.ofReal ((Real.log (Real.exp 1 + 1)) ^ γ) *
            (ENNReal.ofReal ‖ξ‖)⁻¹) := mul_le_mul' hn (mul_le_mul' hl le_rfl)
        _ = _ := one_mul _
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end FalconerThetaGauge
