module

public import FalconerThetaGauge.MaskedDistanceEnergyLowHigh

/-! # Genuine finite dyadic-shell coverage of the high Fourier frequencies -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

/-- The literal dyadic Fourier shell used in source Lemma 7.4. -/
def scalarDyadicFourierShell (v : ℕ) : Set ℝ :=
  {r | (2 : ℝ) ^ ((v : ℝ) - 1) ≤ |r| ∧ |r| ≤ (2 : ℝ) ^ v}

theorem measurableSet_scalarDyadicFourierShell (v : ℕ) :
    MeasurableSet (scalarDyadicFourierShell v) :=
  (isClosed_le continuous_const continuous_abs).measurableSet.inter
    (isClosed_le continuous_abs continuous_const).measurableSet

def scalarDyadicFourierShellIntegral (η : Measure ℝ) (v : ℕ) : ℝ :=
  ∫ r in scalarDyadicFourierShell v, ‖angularScalarFourier η r‖ ^ (2 : ℕ)

/-- Exactly the finite indices `s<v≤t`, including a partial first dyadic shell. -/
def scalarHighDyadicIndices (s : ℝ) (t : ℕ) : Finset ℕ :=
  (Finset.range (t + 1)).filter (fun v ↦ s < (v : ℝ))

theorem scalarFourierAnnulus_subset_dyadicShells {s : ℝ} (hs : 0 ≤ s) (t : ℕ) :
    scalarFourierAnnulus s (t : ℝ) ⊆
      ⋃ v ∈ scalarHighDyadicIndices s t, scalarDyadicFourierShell v := by
  intro r hr
  have hex : ∃ v : ℕ, |r| ≤ (2 : ℝ) ^ v :=
    ⟨t, by simpa only [Real.rpow_natCast] using hr.2⟩
  let v := Nat.find hex
  have hv : |r| ≤ (2 : ℝ) ^ v := Nat.find_spec hex
  have hvt : v ≤ t := Nat.find_min' hex (by simpa only [Real.rpow_natCast] using hr.2)
  have hrv : s < (v : ℝ) := by
    by_contra h
    have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (le_of_not_gt h)
    rw [Real.rpow_natCast] at hpow
    exact (not_le_of_gt hr.1) (hv.trans hpow)
  have hvpos : 0 < v := by
    have : (0 : ℝ) < v := hs.trans_lt hrv
    exact_mod_cast this
  have hlow : (2 : ℝ) ^ ((v : ℝ) - 1) ≤ |r| := by
    have hmin : ¬|r| ≤ (2 : ℝ) ^ (v - 1) := Nat.find_min hex (by dsimp [v]; omega)
    have hvone : 1 ≤ v := hvpos
    have heq : ((v - 1 : ℕ) : ℝ) = (v : ℝ) - 1 := by rw [Nat.cast_sub hvone, Nat.cast_one]
    rw [← heq, Real.rpow_natCast]
    exact (lt_of_not_ge hmin).le
  exact mem_iUnion₂.2 ⟨v, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hrv⟩, hlow, hv⟩

theorem scalarFourierAnnulusIntegral_le_sum_dyadic (η : Measure ℝ) [IsFiniteMeasure η]
    {s : ℝ} (hs : 0 ≤ s) (t : ℕ) :
    scalarFourierAnnulusIntegral η s (t : ℝ) ≤
      ∑ v ∈ scalarHighDyadicIndices s t, scalarDyadicFourierShellIntegral η v := by
  let f := fun r ↦ ‖angularScalarFourier η r‖ ^ (2 : ℕ)
  have hfi (v : ℕ) : Integrable ((scalarDyadicFourierShell v).indicator f) := by
    rw [integrable_indicator_iff (measurableSet_scalarDyadicFourierShell v)]
    apply (((continuous_angularScalarFourier η).norm.pow 2).integrableOn_Icc
      (a := -((2 : ℝ) ^ v)) (b := (2 : ℝ) ^ v)).mono_set
    intro r hr
    exact abs_le.1 hr.2
  have hAnn : Integrable ((scalarFourierAnnulus s (t : ℝ)).indicator f) := by
    rw [integrable_indicator_iff (measurableSet_scalarFourierAnnulus s (t : ℝ))]
    apply (((continuous_angularScalarFourier η).norm.pow 2).integrableOn_Icc
      (a := -((2 : ℝ) ^ t)) (b := (2 : ℝ) ^ t)).mono_set
    intro r hr
    exact abs_le.1 (by simpa only [Real.rpow_natCast] using hr.2)
  have hsum : Integrable (fun r ↦ ∑ v ∈ scalarHighDyadicIndices s t,
      (scalarDyadicFourierShell v).indicator f r) := integrable_finsetSum _ fun v _ ↦ hfi v
  have hpoint : ∀ r : ℝ, (scalarFourierAnnulus s (t : ℝ)).indicator f r ≤
      ∑ v ∈ scalarHighDyadicIndices s t, (scalarDyadicFourierShell v).indicator f r := by
    intro r
    have hnonneg (v : ℕ) : 0 ≤ (scalarDyadicFourierShell v).indicator f r := by
      by_cases hv : r ∈ scalarDyadicFourierShell v <;> simp [hv, f]
    by_cases hr : r ∈ scalarFourierAnnulus s (t : ℝ)
    · obtain ⟨v, hv, hrv⟩ := mem_iUnion₂.1 (scalarFourierAnnulus_subset_dyadicShells hs t hr)
      simpa only [indicator_of_mem hr, indicator_of_mem hrv] using
        Finset.single_le_sum (fun u _ ↦ hnonneg u) hv
    · simpa only [indicator_of_notMem hr] using Finset.sum_nonneg (fun v _ ↦ hnonneg v)
  calc
    _ = ∫ r, (scalarFourierAnnulus s (t : ℝ)).indicator f r :=
      (integral_indicator (measurableSet_scalarFourierAnnulus s (t : ℝ))).symm
    _ ≤ ∫ r, ∑ v ∈ scalarHighDyadicIndices s t, (scalarDyadicFourierShell v).indicator f r :=
      integral_mono hAnn hsum hpoint
    _ = _ := by
      rw [integral_finsetSum _ (fun v _ ↦ hfi v)]
      apply Finset.sum_congr rfl
      intro v _
      exact integral_indicator (measurableSet_scalarDyadicFourierShell v)

/-- The literal finite dyadic high-frequency sum in Lemma 7.4, with the sharper coefficient two. -/
theorem normalizedDistanceCollisionEnergy_le_low_high_dyadic {η β ζ : Measure ℝ}
    [IsFiniteMeasure ζ] (hηβ : η ≤ β) (hβζ : β ≤ ζ) {m s : ℝ}
    (hm : 0 ≤ m) (hs : 0 ≤ s) (t : ℕ) (hst : s ≤ (t : ℝ)) :
    normalizedDistanceCollisionEnergy η m (t : ℝ) ≤
      320 * normalizedDistanceCollisionEnergy ζ m s +
        2 / m * ∑ v ∈ scalarHighDyadicIndices s t, scalarDyadicFourierShellIntegral β v := by
  let : IsFiniteMeasure β := isFiniteMeasure_of_le ζ hβζ
  apply (normalizedDistanceCollisionEnergy_le_low_high hηβ hβζ hm hst).trans
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (scalarFourierAnnulusIntegral_le_sum_dyadic β hs t) (div_nonneg (by norm_num) hm))

/-- The source's exact constant `C₁=320` in the genuine low/high dyadic bridge. -/
theorem normalizedDistanceCollisionEnergy_le_320_low_high_dyadic {η β ζ : Measure ℝ}
    [IsFiniteMeasure ζ] (hηβ : η ≤ β) (hβζ : β ≤ ζ) {m s : ℝ}
    (hm : 0 ≤ m) (hs : 0 ≤ s) (t : ℕ) (hst : s ≤ (t : ℝ)) :
    normalizedDistanceCollisionEnergy η m (t : ℝ) ≤
      320 * normalizedDistanceCollisionEnergy ζ m s +
        320 / m * ∑ v ∈ scalarHighDyadicIndices s t, scalarDyadicFourierShellIntegral β v := by
  apply (normalizedDistanceCollisionEnergy_le_low_high_dyadic hηβ hβζ hm hs t hst).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by norm_num) hm)
  exact Finset.sum_nonneg fun _v _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _)

end FalconerThetaGauge
