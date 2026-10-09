module

public import FalconerThetaGauge.OrthogonalityKernelSpatial
public import FalconerThetaGauge.MaskedFourierArcPair
public import FalconerThetaGauge.FourierSeparationKernel

/-! # The actual spatial Fourier cross term equals the two-pair oscillatory kernel -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped RealInnerProductSpace

namespace FalconerThetaGauge

theorem integral_spatial_orthogonalityCircleKernel (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X X' : Set Plane) (K : ℕ) (ℓ : ℝ)
    (arc : Fin (angularPartitionCount ℓ)) (b : Plane → UnitCircle → ℝ) (r : ℝ)
    (w : UnitCircle) :
    (∫ p : Plane × Plane, orthogonalityCircleKernel K ℓ arc b p.1 p.2 r w
      ∂(ρ₁.restrict X).prod (ρ₂.restrict X')) =
      (equalArcCutoff K ℓ arc w : ℂ) * maskedFourierAmplitude ρ₁ X b r w *
        star (maskedFourierAmplitude ρ₂ X' b r w) := by
  have heq : ∀ p : Plane × Plane, orthogonalityCircleKernel K ℓ arc b p.1 p.2 r w =
      (equalArcCutoff K ℓ arc w : ℂ) * maskedFourierPairKernel b b r w p := by
    intro p
    dsimp only [orthogonalityCircleKernel, orthogonalityCircleAmplitude, maskedFourierPairKernel]
    ring
  simp_rw [heq]
  rw [integral_const_mul, integral_maskedFourierPairKernel]
  ring

theorem maskedFourierArcPairAmplitude_cross_eq (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X X' Y Y' : Set Plane)
    (b₁ b₂ : Plane → UnitCircle → ℝ) (K : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (i j : Fin (angularPartitionCount ℓ)) (z : ℝ × UnitCircle × UnitCircle) :
    maskedFourierArcPairAmplitude ρ₁ ρ₂ X Y b₁ b₂ K ℓ i j z *
      star (maskedFourierArcPairAmplitude ρ₁ ρ₂ X' Y' b₁ b₂ K ℓ i j z) =
      (∫ p : Plane × Plane, orthogonalityCircleKernel K ℓ i b₁ p.1 p.2 z.1 z.2.1
        ∂(ρ₁.restrict X).prod (ρ₁.restrict X')) *
      (∫ p : Plane × Plane, orthogonalityCircleKernel K ℓ j b₂ p.1 p.2 z.1 z.2.2
        ∂(ρ₂.restrict Y).prod (ρ₂.restrict Y')) := by
  rw [integral_spatial_orthogonalityCircleKernel, integral_spatial_orthogonalityCircleKernel]
  have hs (w : UnitCircle) (arc : Fin (angularPartitionCount ℓ)) :
      (Real.sqrt (equalArcCutoff K ℓ arc w) : ℂ) ^ 2 = (equalArcCutoff K ℓ arc w : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (equalArcCutoff_mem_Icc K hℓ arc w).1]
  simp only [maskedFourierArcPairAmplitude, star_mul, Complex.star_def,
    Complex.conj_ofReal, Complex.ofReal_mul]
  have heq : (Real.sqrt (equalArcCutoff K ℓ i z.2.1) : ℂ) ^ 2 *
      (Real.sqrt (equalArcCutoff K ℓ j z.2.2) : ℂ) ^ 2 =
      (equalArcCutoff K ℓ i z.2.1 : ℂ) * (equalArcCutoff K ℓ j z.2.2 : ℂ) := by
    rw [hs, hs]
  calc
    _ = ((Real.sqrt (equalArcCutoff K ℓ i z.2.1) : ℂ) ^ 2 *
        (Real.sqrt (equalArcCutoff K ℓ j z.2.2) : ℂ) ^ 2) *
        (maskedFourierAmplitude ρ₁ X b₁ z.1 z.2.1 *
          (starRingEnd ℂ) (maskedFourierAmplitude ρ₁ X' b₁ z.1 z.2.1) *
          maskedFourierAmplitude ρ₂ Y b₂ z.1 z.2.2 *
          (starRingEnd ℂ) (maskedFourierAmplitude ρ₂ Y' b₂ z.1 z.2.2)) := by ring
    _ = _ := by rw [heq]; ring

theorem integral_joint_orthogonalityCircleKernel_pair (K v : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (i j : Fin (angularPartitionCount ℓ)) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂))
    (hbound₁ : ∀ x w, |b₁ x w| ≤ 1) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    (x x' y y' : Plane) :
    (∫ z : ℝ × UnitCircle × UnitCircle,
      orthogonalityCircleKernel K ℓ i b₁ x x' z.1 z.2.1 *
        orthogonalityCircleKernel K ℓ j b₂ y y' z.1 z.2.2
      ∂maskedFourierJointMeasure K v) =
      orthogonalityTwoPairKernel K v ℓ i j b₁ b₂ x x' y y' := by
  have hi : Integrable (fun z : ℝ × UnitCircle × UnitCircle ↦
      orthogonalityCircleKernel K ℓ i b₁ x x' z.1 z.2.1 *
        orthogonalityCircleKernel K ℓ j b₂ y y' z.1 z.2.2)
      (maskedFourierJointMeasure K v) := by
    apply (integrable_const (1 : ℝ)).mono
    · have h₁ : Measurable (fun z : ℝ × UnitCircle × UnitCircle ↦
          orthogonalityCircleKernel K ℓ i b₁ x x' z.1 z.2.1) :=
        (measurable_orthogonalityCircleKernel K hℓ i hb₁ x x').comp
          (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
      have h₂ : Measurable (fun z : ℝ × UnitCircle × UnitCircle ↦
          orthogonalityCircleKernel K ℓ j b₂ y y' z.1 z.2.2) :=
        (measurable_orthogonalityCircleKernel K hℓ j hb₂ y y').comp
          (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
      exact (h₁.mul h₂).aestronglyMeasurable
    · filter_upwards [] with z
      rw [norm_mul, norm_one]
      exact (mul_le_mul (norm_orthogonalityCircleKernel_le_one K hℓ i hbound₁ x x' _ _)
        (norm_orthogonalityCircleKernel_le_one K hℓ j hbound₂ y y' _ _)
        (norm_nonneg _) (by norm_num)).trans (by norm_num)
  rw [maskedFourierJointMeasure, integral_prod _ hi]
  simp_rw [integral_prod_mul]
  rw [integral_maskedFourierRadialMeasure]
  simp only [Complex.real_smul, ← orthogonalityRadialAmplitude_eq_real_weight,
    orthogonalityTwoPairKernel, mul_assoc]

end FalconerThetaGauge
