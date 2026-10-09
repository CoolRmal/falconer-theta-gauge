module

public import FalconerThetaGauge.MaskedFourierArcPair

/-! # The true partition of the mass-weighted Fourier energy into smoothed arc pairs -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset

namespace FalconerThetaGauge

def maskedFourierArcPairEnergy (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    (b₁ b₂ : Plane → UnitCircle → ℝ) (K v : ℕ) (ℓ : ℝ)
    (i j : Fin (angularPartitionCount ℓ)) : ℝ :=
  ∫ z, ‖maskedFourierArcPairAmplitude ρ₁ ρ₂ X Y b₁ b₂ K ℓ i j z‖ ^ 2
    ∂maskedFourierJointMeasure K v

theorem integrable_maskedFourierJointSquare (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (K v : ℕ) :
    Integrable (fun z : ℝ × UnitCircle × UnitCircle ↦
      ‖maskedFourierAmplitude ρ₁ X b₁ z.1 z.2.1 *
        maskedFourierAmplitude ρ₂ Y b₂ z.1 z.2.2‖ ^ 2) (maskedFourierJointMeasure K v) := by
  have hu₁ : Measurable (fun z : ℝ × UnitCircle × UnitCircle ↦
      maskedFourierAmplitude ρ₁ X b₁ z.1 z.2.1) :=
    (measurable_maskedFourierAmplitude ρ₁ X hb₁).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hu₂ : Measurable (fun z : ℝ × UnitCircle × UnitCircle ↦
      maskedFourierAmplitude ρ₂ Y b₂ z.1 z.2.2) :=
    (measurable_maskedFourierAmplitude ρ₂ Y hb₂).comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  apply (integrable_const ((ρ₁.real X * ρ₂.real Y) ^ 2)).mono
    ((hu₁.mul hu₂).norm.pow_const 2).aestronglyMeasurable
  filter_upwards [] with z
  change |‖maskedFourierAmplitude ρ₁ X b₁ z.1 z.2.1 *
    maskedFourierAmplitude ρ₂ Y b₂ z.1 z.2.2‖ ^ 2| ≤ |(ρ₁.real X * ρ₂.real Y) ^ 2|
  rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _), norm_mul]
  apply pow_le_pow_left₀ (by positivity) _ 2
  exact mul_le_mul (norm_maskedFourierAmplitude_le_mass ρ₁ X hb₁ hbound₁ _ _)
    (norm_maskedFourierAmplitude_le_mass ρ₂ Y hb₂ hbound₂ _ _) (norm_nonneg _)
    measureReal_nonneg

theorem mass_mul_maskedFourierEnergy_joint (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (K v : ℕ) :
    (ρ₁.real X * ρ₂.real Y) * maskedFourierEnergy ρ₁ ρ₂ X Y b₁ b₂ K v =
      ∫ z : ℝ × UnitCircle × UnitCircle,
        ‖maskedFourierAmplitude ρ₁ X b₁ z.1 z.2.1 *
          maskedFourierAmplitude ρ₂ Y b₂ z.1 z.2.2‖ ^ 2 ∂maskedFourierJointMeasure K v := by
  rw [mass_mul_maskedFourierEnergy_radial ρ₁ ρ₂ X Y hb₁ hb₂ hbound₁ hbound₂]
  symm
  exact integral_prod _
    (integrable_maskedFourierJointSquare ρ₁ ρ₂ X Y hb₁ hb₂ hbound₁ hbound₂ K v)

theorem sum_norm_maskedFourierArcPairAmplitude_sq (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    (b₁ b₂ : Plane → UnitCircle → ℝ) (K : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (z : ℝ × UnitCircle × UnitCircle) :
    (∑ i : Fin (angularPartitionCount ℓ), ∑ j : Fin (angularPartitionCount ℓ),
      ‖maskedFourierArcPairAmplitude ρ₁ ρ₂ X Y b₁ b₂ K ℓ i j z‖ ^ 2) =
      ‖maskedFourierAmplitude ρ₁ X b₁ z.1 z.2.1 *
        maskedFourierAmplitude ρ₂ Y b₂ z.1 z.2.2‖ ^ 2 := by
  simp_rw [norm_maskedFourierArcPairAmplitude_sq ρ₁ ρ₂ X Y b₁ b₂ K hℓ]
  have hj : ∀ i, (∑ j : Fin (angularPartitionCount ℓ),
      equalArcCutoff K ℓ i z.2.1 * equalArcCutoff K ℓ j z.2.2 *
        ‖maskedFourierAmplitude ρ₁ X b₁ z.1 z.2.1 *
          maskedFourierAmplitude ρ₂ Y b₂ z.1 z.2.2‖ ^ 2) =
      equalArcCutoff K ℓ i z.2.1 *
        ‖maskedFourierAmplitude ρ₁ X b₁ z.1 z.2.1 *
          maskedFourierAmplitude ρ₂ Y b₂ z.1 z.2.2‖ ^ 2 := by
    intro i
    rw [← sum_mul, ← mul_sum, sum_equalArcCutoff K hℓ, mul_one]
  simp_rw [hj]
  rw [← sum_mul, sum_equalArcCutoff K hℓ, one_mul]

/-- The true `F` partitions exactly into the finitely many smoothed arc-pair energies. -/
theorem sum_maskedFourierArcPairEnergy (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (K v : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∑ i : Fin (angularPartitionCount ℓ), ∑ j : Fin (angularPartitionCount ℓ),
      maskedFourierArcPairEnergy ρ₁ ρ₂ X Y b₁ b₂ K v ℓ i j) =
        (ρ₁.real X * ρ₂.real Y) * maskedFourierEnergy ρ₁ ρ₂ X Y b₁ b₂ K v := by
  have hi : ∀ i j, Integrable (fun z ↦
      ‖maskedFourierArcPairAmplitude ρ₁ ρ₂ X Y b₁ b₂ K ℓ i j z‖ ^ 2)
        (maskedFourierJointMeasure K v) := fun i j ↦
    (memLp_maskedFourierArcPairAmplitude ρ₁ ρ₂ X Y hb₁ hb₂ hbound₁ hbound₂ K v hℓ i j
      ).integrable_norm_pow (by norm_num)
  rw [mass_mul_maskedFourierEnergy_joint ρ₁ ρ₂ X Y hb₁ hb₂ hbound₁ hbound₂]
  simp only [maskedFourierArcPairEnergy]
  have he : ∀ i, (∑ j, ∫ z,
      ‖maskedFourierArcPairAmplitude ρ₁ ρ₂ X Y b₁ b₂ K ℓ i j z‖ ^ 2
        ∂maskedFourierJointMeasure K v) = ∫ z, ∑ j,
      ‖maskedFourierArcPairAmplitude ρ₁ ρ₂ X Y b₁ b₂ K ℓ i j z‖ ^ 2
        ∂maskedFourierJointMeasure K v := fun i ↦
    (integral_finsetSum univ (fun j _ ↦ hi i j)).symm
  simp_rw [he]
  rw [← integral_finsetSum univ (fun i _ ↦ integrable_finsetSum univ (fun j _ ↦ hi i j))]
  apply integral_congr_ae
  filter_upwards [] with z
  exact sum_norm_maskedFourierArcPairAmplitude_sq ρ₁ ρ₂ X Y b₁ b₂ K hℓ z

end FalconerThetaGauge
