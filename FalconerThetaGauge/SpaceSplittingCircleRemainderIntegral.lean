module

public import FalconerThetaGauge.SpaceSplittingCaseAMain
public import FalconerThetaGauge.SpaceSplittingCircleMeasurable

/-! # Integration of the actual stationary remainder against the second circle kernel -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function

namespace FalconerThetaGauge

theorem norm_integral_spaceSplittingCircle_sub_main_le_source
    {ρ : Measure Plane} {θ : ℝ} {N L v : ℕ} (hpar : ParameterFacts θ N)
    {width : ℝ} (I : Finset ProfileScheduleTest) (hcard : I.card ≤ N ^ 2 + 1)
    (hL : L ≤ N) (hlength : ∀ test ∈ I, test.length ≤ L) {h : ℝ}
    (hgap : 2 * max (L : ℝ) (tolerance θ N * N) ≤ (v : ℝ) - h)
    {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ (tolerance θ N * N) width
      (8 * expansionCount θ N) I (2 * expansionCount θ N))
    (hb₂ : Measurable (uncurry b₂)) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    (x x' y y' : Plane) (hd : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ dist x x') :
    ‖(∫ r : ℝ, orthogonalityRadialAmplitude (8 * expansionCount θ N) v r *
        spaceSplittingCircleIntegral b₁ r x x' * spaceSplittingCircleIntegral b₂ r y y') -
      ∫ r : ℝ, orthogonalityRadialAmplitude (8 * expansionCount θ N) v r *
        spaceSplittingStationaryMain (expansionCount θ N) b₁ r x x' *
          spaceSplittingCircleIntegral b₂ r y y'‖ ≤
      64 * (4 : ℝ) ^ v * (2 * Real.pi * (2 : ℝ) ^ (-400 * (N : ℝ))) := by
  have hT : 1 ≤ expansionCount θ N := Nat.ceil_pos.mpr
    (by have := tolerance_pos θ (N := N) (by have := hpar.1; omega); positivity)
  have hb₁m : Measurable (uncurry b₁) := by
    obtain ⟨d, _, rfl⟩ := hb₁
    exact d.measurable_symbol _ _ _ _ _
  have hbound₁ := abs_le_one_of_mem_scheduledSymbolClass ρ _ _ _ _ (by omega) hb₁
  have hd₀ : 0 < dist x x' := lt_of_lt_of_le (by positivity) hd
  have hi := integrable_spaceSplittingCircleIntegral_radial_pair (8 * expansionCount θ N) v
    hb₁m hb₂ hbound₁ hbound₂ x x' y y'
  have him := integrable_spaceSplittingStationaryMain_circle (8 * expansionCount θ N) v
    (expansionCount θ N) b₁ hb₂ hbound₂ x x' y y' hd₀
  have hA : Integrable (orthogonalityRadialAmplitude (8 * expansionCount θ N) v) :=
    (contDiff_orthogonalityRadialAmplitude _ v).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_orthogonalityRadialAmplitude _ v)
  rw [← integral_sub hi him]
  have hbound (r : ℝ) :
      ‖orthogonalityRadialAmplitude (8 * expansionCount θ N) v r *
          spaceSplittingCircleIntegral b₁ r x x' * spaceSplittingCircleIntegral b₂ r y y' -
        orthogonalityRadialAmplitude (8 * expansionCount θ N) v r *
          spaceSplittingStationaryMain (expansionCount θ N) b₁ r x x' *
            spaceSplittingCircleIntegral b₂ r y y'‖ ≤
      ‖orthogonalityRadialAmplitude (8 * expansionCount θ N) v r‖ *
        (2 * Real.pi * (2 : ℝ) ^ (-400 * (N : ℝ))) := by
    by_cases hr : r ∈ tsupport (orthogonalityRadialAmplitude (8 * expansionCount θ N) v)
    · have hr' := (tsupport_orthogonalityRadialAmplitude_subset _ v hr).1
      have he := norm_spaceSplittingCircleIntegral_sub_stationary_le_source hpar I hcard hL
        hlength hb₁ hgap (by simpa only [Real.rpow_natCast] using hr') hd
      rw [show orthogonalityRadialAmplitude (8 * expansionCount θ N) v r *
          spaceSplittingCircleIntegral b₁ r x x' * spaceSplittingCircleIntegral b₂ r y y' -
          orthogonalityRadialAmplitude (8 * expansionCount θ N) v r *
          spaceSplittingStationaryMain (expansionCount θ N) b₁ r x x' *
          spaceSplittingCircleIntegral b₂ r y y' =
        orthogonalityRadialAmplitude (8 * expansionCount θ N) v r *
          (spaceSplittingCircleIntegral b₁ r x x' -
            spaceSplittingStationaryMain (expansionCount θ N) b₁ r x x') *
            spaceSplittingCircleIntegral b₂ r y y' by ring, norm_mul, norm_mul]
      have hA₀ := norm_nonneg (orthogonalityRadialAmplitude (8 * expansionCount θ N) v r)
      have hh := mul_le_mul (mul_le_mul_of_nonneg_left he hA₀)
        (norm_spaceSplittingCircleIntegral_le hb₂ hbound₂ r y y') (norm_nonneg _)
        (mul_nonneg hA₀ (by positivity))
      exact hh.trans_eq (by ring)
    · simp only [image_eq_zero_of_notMem_tsupport hr, zero_mul, sub_self, norm_zero,
        le_refl]
  calc
    _ ≤ ∫ r : ℝ, ‖orthogonalityRadialAmplitude (8 * expansionCount θ N) v r‖ *
        (2 * Real.pi * (2 : ℝ) ^ (-400 * (N : ℝ))) :=
      norm_integral_le_of_norm_le (hA.norm.mul_const _) (Filter.Eventually.of_forall hbound)
    _ = (∫ r : ℝ, ‖orthogonalityRadialAmplitude (8 * expansionCount θ N) v r‖) *
        (2 * Real.pi * (2 : ℝ) ^ (-400 * (N : ℝ))) := integral_mul_const _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (integral_norm_orthogonalityRadialAmplitude_le hT (by omega)) (by positivity)

end FalconerThetaGauge
