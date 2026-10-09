module

public import FalconerThetaGauge.OrthogonalityKernelCrossIdentity

/-! # Genuine Fourier-spatial Fubini for the actual square-root arc cross term -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function

namespace FalconerThetaGauge

def orthogonalitySpatialCircleKernel (K : ℕ) (ℓ : ℝ)
    (i j : Fin (angularPartitionCount ℓ)) (b₁ b₂ : Plane → UnitCircle → ℝ)
    (p : (Plane × Plane) × (Plane × Plane)) (z : ℝ × UnitCircle × UnitCircle) : ℂ :=
  orthogonalityCircleKernel K ℓ i b₁ p.1.1 p.1.2 z.1 z.2.1 *
    orthogonalityCircleKernel K ℓ j b₂ p.2.1 p.2.2 z.1 z.2.2

@[fun_prop]
theorem measurable_orthogonalitySpatialCircleKernel (K : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (i j : Fin (angularPartitionCount ℓ)) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂)) :
    Measurable (uncurry (orthogonalitySpatialCircleKernel K ℓ i j b₁ b₂)) := by
  have h₁ : Measurable (fun q : ((Plane × Plane) × (Plane × Plane)) ×
      (ℝ × UnitCircle × UnitCircle) ↦
      orthogonalityCircleKernel K ℓ i b₁ q.1.1.1 q.1.1.2 q.2.1 q.2.2.1) :=
    (measurable_orthogonalityCircleKernel_joint K hℓ i hb₁).comp
      ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_fst.comp measurable_snd).prodMk
          ((measurable_fst.comp measurable_snd).comp measurable_snd)))
  have h₂ : Measurable (fun q : ((Plane × Plane) × (Plane × Plane)) ×
      (ℝ × UnitCircle × UnitCircle) ↦
      orthogonalityCircleKernel K ℓ j b₂ q.1.2.1 q.1.2.2 q.2.1 q.2.2.2) :=
    (measurable_orthogonalityCircleKernel_joint K hℓ j hb₂).comp
      ((measurable_snd.comp measurable_fst).prodMk
        ((measurable_fst.comp measurable_snd).prodMk
          ((measurable_snd.comp measurable_snd).comp measurable_snd)))
  exact h₁.mul h₂

theorem integrable_orthogonalitySpatialCircleKernel (μ : Measure
    ((Plane × Plane) × (Plane × Plane))) [IsFiniteMeasure μ] (K v : ℕ)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin (angularPartitionCount ℓ))
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) :
    Integrable (uncurry (orthogonalitySpatialCircleKernel K ℓ i j b₁ b₂))
      (μ.prod (maskedFourierJointMeasure K v)) := by
  apply (integrable_const (1 : ℝ)).mono
  · exact (measurable_orthogonalitySpatialCircleKernel K hℓ i j hb₁ hb₂).aestronglyMeasurable
  · filter_upwards [] with q
    rw [uncurry, orthogonalitySpatialCircleKernel, norm_mul, norm_one]
    exact (mul_le_mul (norm_orthogonalityCircleKernel_le_one K hℓ i hbound₁ _ _ _ _)
      (norm_orthogonalityCircleKernel_le_one K hℓ j hbound₂ _ _ _ _)
      (norm_nonneg _) (by norm_num)).trans (by norm_num)

theorem integral_maskedFourierArcPair_cross_eq_spatial (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X X' Y Y' : Set Plane) (K v : ℕ)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin (angularPartitionCount ℓ))
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) :
    (∫ z, maskedFourierArcPairAmplitude ρ₁ ρ₂ X Y b₁ b₂ K ℓ i j z *
      star (maskedFourierArcPairAmplitude ρ₁ ρ₂ X' Y' b₁ b₂ K ℓ i j z)
        ∂maskedFourierJointMeasure K v) =
      ∫ p : (Plane × Plane) × (Plane × Plane),
        orthogonalityTwoPairKernel K v ℓ i j b₁ b₂ p.1.1 p.1.2 p.2.1 p.2.2
        ∂((ρ₁.restrict X).prod (ρ₁.restrict X')).prod
          ((ρ₂.restrict Y).prod (ρ₂.restrict Y')) := by
  let μ := ((ρ₁.restrict X).prod (ρ₁.restrict X')).prod
    ((ρ₂.restrict Y).prod (ρ₂.restrict Y'))
  have hi := integrable_orthogonalitySpatialCircleKernel μ K v hℓ i j hb₁ hb₂ hbound₁ hbound₂
  calc
    _ = ∫ z, ∫ p, orthogonalitySpatialCircleKernel K ℓ i j b₁ b₂ p z
        ∂μ ∂maskedFourierJointMeasure K v := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [maskedFourierArcPairAmplitude_cross_eq _ _ _ _ _ _ _ _ _ hℓ]
      exact (integral_prod_mul _ _).symm
    _ = ∫ p, ∫ z, orthogonalitySpatialCircleKernel K ℓ i j b₁ b₂ p z
        ∂maskedFourierJointMeasure K v ∂μ := (integral_integral_swap hi).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with p
      exact integral_joint_orthogonalityCircleKernel_pair K v hℓ i j hb₁ hb₂ hbound₁ hbound₂
        p.1.1 p.1.2 p.2.1 p.2.2

end FalconerThetaGauge
