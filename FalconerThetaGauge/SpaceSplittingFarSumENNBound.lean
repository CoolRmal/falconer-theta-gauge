/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.SpaceSplittingFarSumWeighted

/-! # True ENNReal pointwise far bounds integrate without pointwise finiteness assumptions -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical RealInnerProductSpace ENNReal

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem spaceSplittingFarCrossSum_le_of_ofReal_majorant (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {a p : ℕ} (hap : a ≤ p)
    (X Y : Fin 2 → ℤ) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂))
    (hbound₁ : ∀ x w, |b₁ x w| ≤ 1) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    (K v : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    {f : (Plane × Plane) × (Plane × Plane) → ℝ≥0∞} (hf : Measurable f)
    (hfin : (∫⁻ z, f z ∂spaceSplittingRootFourMeasure ρ a X Y) ≠ ⊤)
    (hmajor : ∀ P ∈ spaceSplittingFinePairs ρ a p X Y,
      ∀ Q ∈ spaceSplittingFinePairs ρ a p X Y, ¬spaceSplittingNear p P Q →
        ∀ x ∈ dyadicCube p P.1, ∀ x' ∈ dyadicCube p Q.1,
          ∀ y ∈ dyadicCube p P.2, ∀ y' ∈ dyadicCube p Q.2,
            ENNReal.ofReal ‖spaceSplittingAveragedCircleKernel b₁ b₂ K v x x' y y'‖ ≤
              ENNReal.ofReal δ + f ((x, x'), (y, y'))) :
    spaceSplittingFarCrossSum ρ a p X Y b₁ b₂ K v ≤
      δ * (ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y)) ^ 2 +
        (∫⁻ z, f z ∂spaceSplittingRootFourMeasure ρ a X Y).toReal := by
  have hfi := integrable_toReal_of_lintegral_ne_top hf.aemeasurable hfin
  have hi := (integrable_const δ).add hfi
  have hfin' : ∀ P ∈ spaceSplittingFinePairs ρ a p X Y,
      ∀ Q ∈ spaceSplittingFinePairs ρ a p X Y,
        (∫⁻ z, f z ∂spaceSplittingFineFourMeasure ρ p P Q) ≠ ⊤ := by
    rw [← sum_spaceSplittingFineFourMeasure ρ hρ hap X Y,
      lintegral_finsetSum_measure] at hfin
    intro P hP
    have hPfin := ENNReal.sum_ne_top.1 hfin P hP
    rw [lintegral_finsetSum_measure] at hPfin
    exact ENNReal.sum_ne_top.1 hPfin
  have hterm (P : (Fin 2 → ℤ) × (Fin 2 → ℤ))
      (hP : P ∈ spaceSplittingFinePairs ρ a p X Y)
      (Q : (Fin 2 → ℤ) × (Fin 2 → ℤ))
      (hQ : Q ∈ spaceSplittingFinePairs ρ a p X Y) :
      (if spaceSplittingNear p P Q then 0 else
        |∫ z, inner ℝ
          (spaceSplittingJointAmplitude ρ ρ (dyadicCube p P.1) (dyadicCube p P.2) b₁ b₂ z)
          (spaceSplittingJointAmplitude ρ ρ (dyadicCube p Q.1) (dyadicCube p Q.2) b₁ b₂ z)
          ∂maskedFourierJointMeasure K v|) ≤
      ∫ z, δ + (f z).toReal ∂spaceSplittingFineFourMeasure ρ p P Q := by
    by_cases hn : spaceSplittingNear p P Q
    · rw [ite_eq_left hn]
      exact integral_nonneg (fun _ ↦ add_nonneg hδ ENNReal.toReal_nonneg)
    · rw [ite_eq_right hn]
      apply (abs_integral_spaceSplittingJointAmplitude_inner_le_integral_norm ρ ρ
        (dyadicCube p P.1) (dyadicCube p Q.1) (dyadicCube p P.2) (dyadicCube p Q.2)
        K v hb₁ hb₂ hbound₁ hbound₂).trans
      apply integral_mono_ae
        (integrable_spaceSplittingAveragedCircleKernel (spaceSplittingFineFourMeasure ρ p P Q)
          hb₁ hb₂ hbound₁ hbound₂ K v).norm
        (integrable_spaceSplittingFineFourMeasure ρ hρ hap X Y hi hP hQ)
      have hae := ae_mem_four_carriers ρ ρ (measurableSet_dyadicCube p P.1)
        (measurableSet_dyadicCube p Q.1) (measurableSet_dyadicCube p P.2)
        (measurableSet_dyadicCube p Q.2)
      have haeF := ae_lt_top hf (hfin' P hP Q hQ)
      filter_upwards [hae, haeF] with z hz hzf
      have hb := hmajor P hP Q hQ hn z.1.1 hz.1.1 z.1.2 hz.1.2
        z.2.1 hz.2.1 z.2.2 hz.2.2
      have hreal := ENNReal.toReal_mono
        (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hzf.ne⟩) hb
      simpa only [ENNReal.toReal_add ENNReal.ofReal_ne_top hzf.ne,
        ENNReal.toReal_ofReal hδ, ENNReal.toReal_ofReal (norm_nonneg _),
        Pi.add_apply] using hreal
  calc
    _ ≤ ∑ P ∈ spaceSplittingFinePairs ρ a p X Y,
        ∑ Q ∈ spaceSplittingFinePairs ρ a p X Y,
          ∫ z, δ + (f z).toReal ∂spaceSplittingFineFourMeasure ρ p P Q := by
      exact sum_le_sum (fun P hP ↦ sum_le_sum (fun Q hQ ↦ hterm P hP Q hQ))
    _ = ∫ z, δ + (f z).toReal ∂spaceSplittingRootFourMeasure ρ a X Y :=
      sum_integral_spaceSplittingFineFourMeasure ρ hρ hap X Y hi
    _ = _ := by
      rw [integral_add (integrable_const δ) hfi, integral_const,
        spaceSplittingRootFourMeasure_real_univ, smul_eq_mul, mul_comm,
        integral_toReal hf.aemeasurable (ae_lt_top hf hfin)]

end FalconerThetaGauge
