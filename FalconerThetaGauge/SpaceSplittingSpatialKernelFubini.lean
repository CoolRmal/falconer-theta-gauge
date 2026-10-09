/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.SpaceSplittingSpatialKernel

/-! # True four-point spatial Fubini for the space-splitting cross term -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped RealInnerProductSpace

namespace FalconerThetaGauge

def spaceSplittingSpatialCircleKernel (b₁ b₂ : Plane → UnitCircle → ℝ)
    (p : (Plane × Plane) × (Plane × Plane)) (z : ℝ × UnitCircle × UnitCircle) : ℂ :=
  maskedFourierPairKernel b₁ b₁ z.1 z.2.1 p.1 *
    maskedFourierPairKernel b₂ b₂ z.1 z.2.2 p.2

@[fun_prop]
theorem measurable_spaceSplittingSpatialCircleKernel {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂)) :
    Measurable (uncurry (spaceSplittingSpatialCircleKernel b₁ b₂)) := by
  have h₁ : Measurable (fun q : ((Plane × Plane) × (Plane × Plane)) ×
      (ℝ × UnitCircle × UnitCircle) ↦
      maskedFourierPairKernel b₁ b₁ q.2.1 q.2.2.1 q.1.1) :=
    (measurable_maskedFourierPairKernel_joint hb₁ hb₁).comp
      ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_fst.comp measurable_snd).prodMk
          ((measurable_fst.comp measurable_snd).comp measurable_snd)))
  have h₂ : Measurable (fun q : ((Plane × Plane) × (Plane × Plane)) ×
      (ℝ × UnitCircle × UnitCircle) ↦
      maskedFourierPairKernel b₂ b₂ q.2.1 q.2.2.2 q.1.2) :=
    (measurable_maskedFourierPairKernel_joint hb₂ hb₂).comp
      ((measurable_snd.comp measurable_fst).prodMk
        ((measurable_fst.comp measurable_snd).prodMk
          ((measurable_snd.comp measurable_snd).comp measurable_snd)))
  exact h₁.mul h₂

theorem norm_spaceSplittingSpatialCircleKernel_le_one
    {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hbound₁ : ∀ x w, |b₁ x w| ≤ 1) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    (p : (Plane × Plane) × (Plane × Plane)) (z : ℝ × UnitCircle × UnitCircle) :
    ‖spaceSplittingSpatialCircleKernel b₁ b₂ p z‖ ≤ 1 := by
  have h (b : Plane → UnitCircle → ℝ) (hb : ∀ x w, |b x w| ≤ 1)
      (r : ℝ) (w : UnitCircle) (q : Plane × Plane) :
      ‖maskedFourierPairKernel b b r w q‖ ≤ 1 := by
    rw [norm_maskedFourierPairKernel]
    exact (mul_le_mul (hb _ _) (hb _ _) (abs_nonneg _) (by norm_num)).trans
      (by norm_num)
  rw [spaceSplittingSpatialCircleKernel, norm_mul]
  exact (mul_le_mul (h b₁ hbound₁ _ _ _) (h b₂ hbound₂ _ _ _)
    (norm_nonneg _) (by norm_num)).trans (by norm_num)

theorem integrable_spaceSplittingSpatialCircleKernel
    (μ : Measure ((Plane × Plane) × (Plane × Plane))) [IsFiniteMeasure μ] (K v : ℕ)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) :
    Integrable (uncurry (spaceSplittingSpatialCircleKernel b₁ b₂))
      (μ.prod (maskedFourierJointMeasure K v)) := by
  apply (integrable_const (1 : ℝ)).mono
  · exact (measurable_spaceSplittingSpatialCircleKernel hb₁ hb₂).aestronglyMeasurable
  · filter_upwards [] with q
    rw [norm_one]
    exact norm_spaceSplittingSpatialCircleKernel_le_one hbound₁ hbound₂ q.1 q.2

theorem integral_joint_spaceSplittingSpatialCircleKernel (K v : ℕ)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    (p : (Plane × Plane) × (Plane × Plane)) :
    (∫ z, spaceSplittingSpatialCircleKernel b₁ b₂ p z ∂maskedFourierJointMeasure K v) =
      spaceSplittingAveragedCircleKernel b₁ b₂ K v p.1.1 p.1.2 p.2.1 p.2.2 := by
  have hm : Measurable (spaceSplittingSpatialCircleKernel b₁ b₂ p) :=
    (measurable_spaceSplittingSpatialCircleKernel hb₁ hb₂).comp
      (measurable_const.prodMk measurable_id)
  have hi : Integrable (spaceSplittingSpatialCircleKernel b₁ b₂ p)
      (maskedFourierJointMeasure K v) := by
    apply (integrable_const (1 : ℝ)).mono hm.aestronglyMeasurable
    filter_upwards [] with z
    rw [norm_one]
    exact norm_spaceSplittingSpatialCircleKernel_le_one hbound₁ hbound₂ p z
  rw [spaceSplittingAveragedCircleKernel_eq_radial, maskedFourierJointMeasure,
    integral_prod _ hi]
  simp only [spaceSplittingSpatialCircleKernel, spaceSplittingCircleIntegral]
  apply integral_congr_ae
  filter_upwards [] with r
  exact integral_prod_mul (fun w : UnitCircle ↦ maskedFourierPairKernel b₁ b₁ r w p.1)
    (fun w : UnitCircle ↦ maskedFourierPairKernel b₂ b₂ r w p.2)

theorem spaceSplittingJointAmplitude_cross_eq_spatial (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X X' Y Y' : Set Plane)
    (b₁ b₂ : Plane → UnitCircle → ℝ) (z : ℝ × UnitCircle × UnitCircle) :
    spaceSplittingJointAmplitude ρ₁ ρ₂ X Y b₁ b₂ z *
      star (spaceSplittingJointAmplitude ρ₁ ρ₂ X' Y' b₁ b₂ z) =
      ∫ p : (Plane × Plane) × (Plane × Plane), spaceSplittingSpatialCircleKernel b₁ b₂ p z
        ∂((ρ₁.restrict X).prod (ρ₁.restrict X')).prod
          ((ρ₂.restrict Y).prod (ρ₂.restrict Y')) := by
  simp only [spaceSplittingSpatialCircleKernel]
  rw [integral_prod_mul,
    integral_maskedFourierPairKernel, integral_maskedFourierPairKernel]
  simp only [spaceSplittingJointAmplitude, star_mul]
  ring

theorem integral_spaceSplittingJointAmplitude_cross_eq_spatial (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X X' Y Y' : Set Plane) (K v : ℕ)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) :
    (∫ z, spaceSplittingJointAmplitude ρ₁ ρ₂ X Y b₁ b₂ z *
      star (spaceSplittingJointAmplitude ρ₁ ρ₂ X' Y' b₁ b₂ z)
      ∂maskedFourierJointMeasure K v) =
      ∫ p : (Plane × Plane) × (Plane × Plane),
        spaceSplittingAveragedCircleKernel b₁ b₂ K v p.1.1 p.1.2 p.2.1 p.2.2
        ∂((ρ₁.restrict X).prod (ρ₁.restrict X')).prod
          ((ρ₂.restrict Y).prod (ρ₂.restrict Y')) := by
  let μ := ((ρ₁.restrict X).prod (ρ₁.restrict X')).prod
    ((ρ₂.restrict Y).prod (ρ₂.restrict Y'))
  have hi := integrable_spaceSplittingSpatialCircleKernel μ K v hb₁ hb₂ hbound₁ hbound₂
  calc
    _ = ∫ z, ∫ p, spaceSplittingSpatialCircleKernel b₁ b₂ p z
        ∂μ ∂maskedFourierJointMeasure K v := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact spaceSplittingJointAmplitude_cross_eq_spatial ρ₁ ρ₂ X X' Y Y' b₁ b₂ z
    _ = ∫ p, ∫ z, spaceSplittingSpatialCircleKernel b₁ b₂ p z
        ∂maskedFourierJointMeasure K v ∂μ := (integral_integral_swap hi).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with p
      exact integral_joint_spaceSplittingSpatialCircleKernel K v hb₁ hb₂ hbound₁ hbound₂ p

theorem integral_spaceSplittingJointAmplitude_inner_eq_spatial (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X X' Y Y' : Set Plane) (K v : ℕ)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) :
    (∫ z, inner ℝ (spaceSplittingJointAmplitude ρ₁ ρ₂ X Y b₁ b₂ z)
      (spaceSplittingJointAmplitude ρ₁ ρ₂ X' Y' b₁ b₂ z)
      ∂maskedFourierJointMeasure K v) =
      (∫ p : (Plane × Plane) × (Plane × Plane),
        spaceSplittingAveragedCircleKernel b₁ b₂ K v p.1.1 p.1.2 p.2.1 p.2.2
        ∂((ρ₁.restrict X).prod (ρ₁.restrict X')).prod
          ((ρ₂.restrict Y).prod (ρ₂.restrict Y'))).re := by
  have hf := memLp_spaceSplittingJointAmplitude ρ₁ ρ₂ X Y hb₁ hb₂ hbound₁ hbound₂ K v
  have hg := memLp_spaceSplittingJointAmplitude ρ₁ ρ₂ X' Y'
    hb₁ hb₂ hbound₁ hbound₂ K v
  have he (z : ℝ × UnitCircle × UnitCircle) :
      inner ℝ (spaceSplittingJointAmplitude ρ₁ ρ₂ X Y b₁ b₂ z)
        (spaceSplittingJointAmplitude ρ₁ ρ₂ X' Y' b₁ b₂ z) =
      (spaceSplittingJointAmplitude ρ₁ ρ₂ X Y b₁ b₂ z *
        star (spaceSplittingJointAmplitude ρ₁ ρ₂ X' Y' b₁ b₂ z)).re := by
    rw [← real_inner_comm]
    exact Complex.inner _ _
  simp_rw [he]
  change (∫ z, RCLike.re (spaceSplittingJointAmplitude ρ₁ ρ₂ X Y b₁ b₂ z *
    star (spaceSplittingJointAmplitude ρ₁ ρ₂ X' Y' b₁ b₂ z))
    ∂maskedFourierJointMeasure K v) = _
  rw [integral_re (integrable_complex_cross_of_memLp_two hf hg),
    integral_spaceSplittingJointAmplitude_cross_eq_spatial ρ₁ ρ₂ X X' Y Y' K v
      hb₁ hb₂ hbound₁ hbound₂]
  rfl

end FalconerThetaGauge
