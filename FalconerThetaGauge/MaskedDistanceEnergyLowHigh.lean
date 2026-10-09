module

public import FalconerThetaGauge.MaskedDistanceEnergyReal

/-! # The genuine low/high Fourier decomposition for source Lemma 7.4 -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function

namespace FalconerThetaGauge

/-- The literal high-frequency annulus between two real dyadic exponents. -/
def scalarFourierAnnulus (s t : ℝ) : Set ℝ :=
  {r | (2 : ℝ) ^ s < |r| ∧ |r| ≤ (2 : ℝ) ^ t}

theorem measurableSet_scalarFourierAnnulus (s t : ℝ) : MeasurableSet (scalarFourierAnnulus s t) :=
  (isOpen_lt continuous_const continuous_abs).measurableSet.inter
    (isClosed_le continuous_abs continuous_const).measurableSet

/-- The actual angular Fourier energy in that annulus. -/
def scalarFourierAnnulusIntegral (η : Measure ℝ) (s t : ℝ) : ℝ :=
  ∫ r in scalarFourierAnnulus s t, ‖angularScalarFourier η r‖ ^ (2 : ℕ)

theorem scalarFourierAnnulusIntegral_nonneg (η : Measure ℝ) (s t : ℝ) :
    0 ≤ scalarFourierAnnulusIntegral η s t := integral_nonneg fun _ ↦ sq_nonneg _

/-- The two actual Fourier windows split exactly into low and high frequencies. -/
theorem scalarFourierWindowIntegral_eq_low_add_annulus (η : Measure ℝ)
    [IsFiniteMeasure η] {s t : ℝ} (hst : s ≤ t) :
    scalarFourierWindowIntegral η ((2 : ℝ) ^ t) =
      scalarFourierWindowIntegral η ((2 : ℝ) ^ s) + scalarFourierAnnulusIntegral η s t := by
  have hpow : (2 : ℝ) ^ s ≤ (2 : ℝ) ^ t :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hst
  have hsub : Icc (-((2 : ℝ) ^ s)) ((2 : ℝ) ^ s) ⊆ Icc (-((2 : ℝ) ^ t)) ((2 : ℝ) ^ t) :=
    Icc_subset_Icc (neg_le_neg hpow) hpow
  have hset : scalarFourierAnnulus s t =
      Icc (-((2 : ℝ) ^ t)) ((2 : ℝ) ^ t) \ Icc (-((2 : ℝ) ^ s)) ((2 : ℝ) ^ s) := by
    ext r
    simp only [scalarFourierAnnulus, mem_ofPred_eq, mem_sdiff, mem_Icc, ← abs_le, not_le]
    exact and_comm
  unfold scalarFourierAnnulusIntegral scalarFourierWindowIntegral
  rw [hset, setIntegral_sdiff (f := fun r ↦ ‖angularScalarFourier η r‖ ^ (2 : ℕ)) measurableSet_Icc
    (((continuous_angularScalarFourier η).norm.pow 2).integrableOn_Icc) hsub]
  ring

/-- The analytic content of Lemma 7.4: two genuine positive-measure comparisons,
the proved binning bounds, and an exact Fourier-window split give constants 320 and two. -/
theorem normalizedDistanceCollisionEnergy_le_low_high {η β ζ : Measure ℝ}
    [IsFiniteMeasure ζ] (hηβ : η ≤ β) (hβζ : β ≤ ζ) {m s t : ℝ}
    (hm : 0 ≤ m) (hst : s ≤ t) :
    normalizedDistanceCollisionEnergy η m t ≤
      320 * normalizedDistanceCollisionEnergy ζ m s +
        2 / m * scalarFourierAnnulusIntegral β s t := by
  let : IsFiniteMeasure β := isFiniteMeasure_of_le ζ hβζ
  let : IsFiniteMeasure η := isFiniteMeasure_of_le β hηβ
  calc
    _ ≤ normalizedDistanceCollisionEnergy β m t :=
      normalizedDistanceCollisionEnergy_mono hηβ hm t
    _ ≤ 2 / m * scalarFourierWindowIntegral β ((2 : ℝ) ^ t) :=
      normalizedDistanceCollisionEnergy_le_two_fourier β hm t
    _ = 2 / m * scalarFourierWindowIntegral β ((2 : ℝ) ^ s) +
        2 / m * scalarFourierAnnulusIntegral β s t := by
      rw [scalarFourierWindowIntegral_eq_low_add_annulus β hst, mul_add]
    _ ≤ 320 * normalizedDistanceCollisionEnergy β m s +
        2 / m * scalarFourierAnnulusIntegral β s t :=
      add_le_add (two_normalized_fourier_le_320_distance β hm s) le_rfl
    _ ≤ _ := by
      exact add_le_add (mul_le_mul_of_nonneg_left
        (normalizedDistanceCollisionEnergy_mono hβζ hm s) (by norm_num : (0 : ℝ) ≤ 320)) le_rfl

end FalconerThetaGauge
