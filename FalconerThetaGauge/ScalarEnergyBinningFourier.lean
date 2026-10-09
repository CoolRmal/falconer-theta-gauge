module

public import FalconerThetaGauge.ScalarEnergyBinningFourierAverages

/-!
# The Fourier comparison in Lemma 7.3(iv)

The literal angular-frequency Fourier window is compared to the collision
mass. The proof evaluates the positive two-interval average and uses the
scalar binning kernel bound from part (iii).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal

namespace FalconerThetaGauge

/-- The actual squared Fourier modulus integrated over a centered angular-frequency window. -/
def scalarFourierWindowIntegral (η : Measure ℝ) (R : ℝ) : ℝ :=
  ∫ r in Icc (-R) R, ‖angularScalarFourier η r‖ ^ (2 : ℕ)

theorem scalarFourierWindowIntegral_nonneg (η : Measure ℝ) (R : ℝ) :
    0 ≤ scalarFourierWindowIntegral η R := integral_nonneg fun _ ↦ sq_nonneg _

theorem integrable_scalar_sinc_sq (η : Measure ℝ) [IsFiniteMeasure η] (A : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦ Real.sinc (A * (p.1 - p.2)) ^ (2 : ℕ)) (η.prod η) := by
  apply (integrable_const (1 : ℝ)).mono (by fun_prop)
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_one]
  have hs := abs_le.1 (Real.abs_sinc_le_one (A * (p.1 - p.2)))
  nlinarith [hs.1, hs.2]

theorem integrable_scalar_decay (η : Measure ℝ) [IsFiniteMeasure η]
    {h : ℝ} (hh : 0 < h) :
    Integrable (fun p : ℝ × ℝ ↦ (1 + |p.1 - p.2| / h) ^ (-2 : ℝ)) (η.prod η) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ ↦
      (1 + |p.1 - p.2| / h) ^ (-2 : ℝ)) (η.prod η) := by
    have hc : Continuous (fun p : ℝ × ℝ ↦ (1 + |p.1 - p.2| / h) ^ (-2 : ℝ)) := by
      apply Continuous.rpow_const (by fun_prop)
      intro p
      left
      have hp : 0 < 1 + |p.1 - p.2| / h := by positivity
      exact hp.ne'
    exact hc.aestronglyMeasurable
  apply (integrable_const (1 : ℝ)).mono hm
  filter_upwards [] with p
  have hb : 1 ≤ 1 + |p.1 - p.2| / h :=
    le_add_of_nonneg_right (div_nonneg (abs_nonneg _) hh.le)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  simpa using Real.rpow_le_rpow_of_nonpos zero_lt_one hb (by norm_num : (-2 : ℝ) ≤ 0)

theorem integral_scalar_decay_le_ten_collision (η : Measure ℝ) [IsFiniteMeasure η]
    {h : ℝ} (hh : 0 < h) :
    (∫ p : ℝ × ℝ, (1 + |p.1 - p.2| / h) ^ (-2 : ℝ) ∂η.prod η) ≤
      10 * (scalarCollisionMass η η h 0).toReal := by
  have hc : (scalarCollisionMass η η h 0 * scalarCollisionMass η η h 0) ^ (1 / 2 : ℝ) =
      scalarCollisionMass η η h 0 := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ENNReal.rpow_add_of_nonneg (1 / 2 : ℝ) (1 / 2 : ℝ)
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  have hb := lintegral_scalarBinningKernel_le_ten η η hh
  rw [hc] at hb
  have ht : 10 * scalarCollisionMass η η h 0 ≠ ⊤ := by
    unfold scalarCollisionMass
    finiteness
  have hr := ENNReal.toReal_mono ht hb
  unfold scalarBinningKernel at hr
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_scalar_decay η hh)
    (Eventually.of_forall fun p ↦ Real.rpow_nonneg (by positivity) _)] at hr
  have hi₀ : 0 ≤ ∫ p : ℝ × ℝ, (1 + |p.1 - p.2| / h) ^ (-2 : ℝ) ∂η.prod η :=
    integral_nonneg fun p ↦ Real.rpow_nonneg (by positivity) _
  rw [ENNReal.toReal_ofReal hi₀] at hr
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] using hr

/-- Collision mass is controlled by the positive Fejér spatial kernel. -/
theorem scalarCollisionMass_toReal_le_sinc_sq (η : Measure ℝ) [IsFiniteMeasure η]
    {h : ℝ} (hh : 0 < h) :
    (scalarCollisionMass η η h 0).toReal ≤
      2 * ∫ p : ℝ × ℝ, Real.sinc ((p.1 - p.2) / (2 * h)) ^ (2 : ℕ) ∂η.prod η := by
  let S : Set (ℝ × ℝ) := {p | |p.1 - p.2| ≤ h}
  have hm : MeasurableSet S := by
    simpa only [S, sub_zero] using measurableSet_scalarCollision h 0
  have hbound (p : ℝ × ℝ) :
      S.indicator (fun _ ↦ (1 : ℝ)) p ≤ 2 * Real.sinc ((p.1 - p.2) / (2 * h)) ^ (2 : ℕ) := by
    by_cases hp : p ∈ S
    · rw [indicator_of_mem hp]
      have hu : |(p.1 - p.2) / (2 * h)| ≤ 1 / 2 := by
        rw [abs_div, abs_of_pos (by positivity : 0 < 2 * h)]
        apply (div_le_iff₀ (by positivity : 0 < 2 * h)).2
        dsimp [S] at hp
        linarith
      linarith [half_le_sinc_sq_of_abs_le_half hu]
    · rw [indicator_of_notMem hp]
      positivity
  have hi : Integrable (fun p : ℝ × ℝ ↦ Real.sinc ((p.1 - p.2) / (2 * h)) ^ (2 : ℕ))
      (η.prod η) := by
    simpa only [div_eq_mul_inv, mul_comm _ (2 * h)⁻¹] using
      integrable_scalar_sinc_sq η (2 * h)⁻¹
  have hb := integral_mono ((integrable_const (1 : ℝ)).indicator hm) (hi.const_mul 2) hbound
  rw [integral_indicator hm, setIntegral_const, smul_eq_mul, mul_one,
    integral_const_mul] at hb
  simpa only [scalarCollisionMass, sub_zero, Measure.real, S] using hb

/-- A scalar-factor form of the exact positive box identity. -/
theorem integral_integral_fourier_box_eq_mul_sinc_sq (η : Measure ℝ) [IsFiniteMeasure η]
    {A : ℝ} (hA : 0 ≤ A) :
    (∫ t in Icc (-A) A, ∫ u in Icc (-A) A,
      ‖angularScalarFourier η (t + u)‖ ^ (2 : ℕ)) =
      4 * A ^ (2 : ℕ) *
        ∫ p : ℝ × ℝ, Real.sinc (A * (p.1 - p.2)) ^ (2 : ℕ) ∂η.prod η := by
  rw [integral_integral_fourier_box_eq_sinc_sq η hA]
  simp_rw [mul_pow]
  rw [integral_const_mul]
  ring

/-- The first Fourier comparison in Lemma 7.3(iv), with the source constant two. -/
theorem scalarCollisionMass_toReal_le_two_mul_fourier (η : Measure ℝ) [IsFiniteMeasure η]
    {h : ℝ} (hh : 0 < h) :
    (scalarCollisionMass η η h 0).toReal ≤
      2 * h * scalarFourierWindowIntegral η (1 / h) := by
  let A : ℝ := (2 * h)⁻¹
  let S : ℝ := ∫ p : ℝ × ℝ, Real.sinc (A * (p.1 - p.2)) ^ (2 : ℕ) ∂η.prod η
  let B : ℝ := ∫ t in Icc (-A) A, ∫ u in Icc (-A) A,
    ‖angularScalarFourier η (t + u)‖ ^ (2 : ℕ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hid : B = 4 * A ^ (2 : ℕ) * S :=
    integral_integral_fourier_box_eq_mul_sinc_sq η hA
  have hcoef : h ^ (2 : ℕ) * (4 * A ^ (2 : ℕ)) = 1 := by
    dsimp [A]
    field_simp
    ring
  have hrel : S = h ^ (2 : ℕ) * B := by
    rw [hid, ← mul_assoc, hcoef, one_mul]
  have hf : Continuous (fun r ↦ ‖angularScalarFourier η r‖ ^ (2 : ℕ)) :=
    (continuous_angularScalarFourier η).norm.pow 2
  have hb : B ≤ 2 * A * scalarFourierWindowIntegral η (2 * A) :=
    integral_positive_box_average_le hf (fun r ↦ sq_nonneg _) hA
  have hR : 2 * A = 1 / h := by dsimp [A]; field_simp
  have hc : (scalarCollisionMass η η h 0).toReal ≤ 2 * S := by
    simpa only [S, A, div_eq_mul_inv, mul_comm _ (2 * h)⁻¹] using
      scalarCollisionMass_toReal_le_sinc_sq η hh
  calc
    _ ≤ 2 * S := hc
    _ = 2 * h ^ (2 : ℕ) * B := by rw [hrel]; ring
    _ ≤ 2 * h ^ (2 : ℕ) * (2 * A * scalarFourierWindowIntegral η (2 * A)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by
      rw [hR]
      field_simp

/-- The second Fourier comparison in Lemma 7.3(iv), with the source constant 160. -/
theorem scalarFourierWindowIntegral_le_160_collision (η : Measure ℝ) [IsFiniteMeasure η]
    {h : ℝ} (hh : 0 < h) :
    scalarFourierWindowIntegral η (1 / h) ≤
      160 / h * (scalarCollisionMass η η h 0).toReal := by
  let A : ℝ := 1 / h
  let S : ℝ := ∫ p : ℝ × ℝ, Real.sinc (A * (p.1 - p.2)) ^ (2 : ℕ) ∂η.prod η
  let B : ℝ := ∫ t in Icc (-A) A, ∫ u in Icc (-A) A,
    ‖angularScalarFourier η (t + u)‖ ^ (2 : ℕ)
  let D : ℝ := ∫ p : ℝ × ℝ, (1 + |p.1 - p.2| / h) ^ (-2 : ℝ) ∂η.prod η
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hid : B = 4 * A ^ (2 : ℕ) * S :=
    integral_integral_fourier_box_eq_mul_sinc_sq η hA
  have hf : Continuous (fun r ↦ ‖angularScalarFourier η r‖ ^ (2 : ℕ)) :=
    (continuous_angularScalarFourier η).norm.pow 2
  have hb : A * scalarFourierWindowIntegral η A ≤ B :=
    mul_integral_le_positive_box_average hf (fun r ↦ sq_nonneg _) hA
  have hsmall : scalarFourierWindowIntegral η A ≤ h * B := by
    have hmul := mul_le_mul_of_nonneg_left hb hh.le
    have hprod : h * A = 1 := by dsimp [A]; field_simp
    simpa only [← mul_assoc, hprod, one_mul] using hmul
  have henv : 4 * S ≤ 16 * D := by
    have hp (p : ℝ × ℝ) :
        4 * Real.sinc (A * (p.1 - p.2)) ^ (2 : ℕ) ≤
          16 * (1 + |p.1 - p.2| / h) ^ (-2 : ℝ) := by
      simpa only [A, div_mul_eq_mul_div, one_mul, abs_div, abs_of_pos hh] using
        four_mul_sinc_sq_le_decay ((p.1 - p.2) / h)
    have hi := integral_mono ((integrable_scalar_sinc_sq η A).const_mul 4)
      ((integrable_scalar_decay η hh).const_mul 16) hp
    simpa only [integral_const_mul, S, D] using hi
  calc
    _ ≤ h * B := hsmall
    _ = (1 / h) * (4 * S) := by
      rw [hid]
      dsimp [A]
      field_simp
    _ ≤ (1 / h) * (16 * D) := mul_le_mul_of_nonneg_left henv (by positivity)
    _ ≤ (1 / h) * (16 * (10 * (scalarCollisionMass η η h 0).toReal)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (integral_scalar_decay_le_ten_collision η hh) (by norm_num))
        (by positivity)
    _ = _ := by ring

/-- The first estimate also retains its exact extended-measure statement. -/
theorem scalarCollisionMass_le_two_mul_fourier (η : Measure ℝ) [IsFiniteMeasure η]
    {h : ℝ} (hh : 0 < h) :
    scalarCollisionMass η η h 0 ≤
      ENNReal.ofReal (2 * h * scalarFourierWindowIntegral η (1 / h)) := by
  have hc : scalarCollisionMass η η h 0 ≠ ⊤ := by unfold scalarCollisionMass; finiteness
  rw [← ENNReal.ofReal_toReal hc]
  exact ENNReal.ofReal_le_ofReal (scalarCollisionMass_toReal_le_two_mul_fourier η hh)

/-- Extended squared Fourier energy, with the same literal frequency window. -/
def scalarFourierWindowEnergy (η : Measure ℝ) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Icc (-R) R, ENNReal.ofReal (‖angularScalarFourier η r‖ ^ (2 : ℕ))

theorem scalarFourierWindowEnergy_eq_ofReal (η : Measure ℝ) [IsFiniteMeasure η] (R : ℝ) :
    scalarFourierWindowEnergy η R = ENNReal.ofReal (scalarFourierWindowIntegral η R) := by
  exact (ofReal_integral_eq_lintegral_ofReal
    (((continuous_angularScalarFourier η).norm.pow 2).integrableOn_Icc)
    (Eventually.of_forall fun r ↦ sq_nonneg _)).symm

/-- The literal extended-measure lower Fourier estimate in source Lemma 7.3(iv). -/
theorem scalarCollisionMass_le_two_mul_fourierEnergy (η : Measure ℝ) [IsFiniteMeasure η]
    {h : ℝ} (hh : 0 < h) :
    scalarCollisionMass η η h 0 ≤
      ENNReal.ofReal (2 * h) * scalarFourierWindowEnergy η (1 / h) := by
  rw [scalarFourierWindowEnergy_eq_ofReal, ← ENNReal.ofReal_mul (by positivity)]
  exact scalarCollisionMass_le_two_mul_fourier η hh

/-- The literal extended-measure upper Fourier estimate in source Lemma 7.3(iv). -/
theorem scalarFourierWindowEnergy_le_160_collision (η : Measure ℝ) [IsFiniteMeasure η]
    {h : ℝ} (hh : 0 < h) :
    scalarFourierWindowEnergy η (1 / h) ≤
      ENNReal.ofReal (160 / h) * scalarCollisionMass η η h 0 := by
  have hc : scalarCollisionMass η η h 0 ≠ ⊤ := by unfold scalarCollisionMass; finiteness
  rw [scalarFourierWindowEnergy_eq_ofReal, ← ENNReal.ofReal_toReal hc,
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (scalarFourierWindowIntegral_le_160_collision η hh)

end FalconerThetaGauge
