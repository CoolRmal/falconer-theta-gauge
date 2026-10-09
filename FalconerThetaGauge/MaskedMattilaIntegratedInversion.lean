/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.MaskedMattilaDistanceFourier

/-! # Actual spatial integration of the source Mattila inversion error -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric Finset
open scoped Classical ContDiff

namespace FalconerThetaGauge

theorem norm_integral_sub_le_const {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsFiniteMeasure μ] {f g : A → ℂ} (hf : Integrable f μ)
    (hg : Integrable g μ) {ε : ℝ} (hbound : ∀ᵐ x ∂μ, ‖f x - g x‖ ≤ ε) :
    ‖(∫ x, f x ∂μ) - ∫ x, g x ∂μ‖ ≤ ε * μ.real univ := by
  rw [← integral_sub hf hg]
  calc
    _ ≤ ∫ x, ‖f x - g x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ _x, ε ∂μ := integral_mono_ae (hf.sub hg).norm (integrable_const _) hbound
    _ = _ := by simp [mul_comm]

theorem integrable_spatial_preparedInverseCircleKernelSeries (T : ℕ) (α : ℝ)
    (d₁ d₂ : ScheduledSymbolData)
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    {X Y : Set Plane} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hXball : X ⊆ closedBall x₀ ρ) (hYball : Y ⊆ closedBall y₀ ρ)
    (E width : ℝ) (K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest)
    (horder₁ : d₁.order I₁ + 2 * T ≤ K)
    (horder₂ : d₂.order I₂ + 2 * T ≤ K) (r : ℝ) :
    Integrable (fun z : Plane × Plane ↦ preparedInverseCircleKernelSeries T α
      (builtSymbolPairAngularAmplitude (d₁.symbol ρ₁ E width K I₁)
        (d₂.symbol ρ₂ E width K I₂) z.1 z.2) (z.1 - z.2) r)
        ((ρ₁.restrict X).prod (ρ₂.restrict Y)) := by
  have hc (j : ℕ) (z : Plane × Plane) :
      ((r * ‖z.1 - z.2‖ : ℝ) : ℂ)⁻¹ ^ j =
        (r : ℂ)⁻¹ ^ j * (((dist z.1 z.2)⁻¹ ^ j : ℝ) : ℂ) := by
    simp only [← dist_eq_norm, Complex.ofReal_mul, mul_inv_rev, mul_pow,
      Complex.ofReal_pow, Complex.ofReal_inv]
    ring
  simp only [preparedInverseCircleKernelSeries, hc, mul_assoc]
  apply integrable_finsetSum
  intro j hj
  have := Finset.mem_range.mp hj
  have := stationaryPhaseInversePolynomial_natDegree_le j
  exact (integrable_spatial_preparedInverseCircleKernel j T α d₁ d₂ ρ₁ ρ₂ hρ hsep hX hY
    hXball hYball E width K I₁ I₂ (by omega) (by omega) r).const_mul _

set_option maxHeartbeats 800000 in
theorem norm_maskedDistance_mattila_inversion_error {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N)
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    {X Y : Set Plane} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hXball : X ⊆ closedBall x₀ ρ) (hYball : Y ⊆ closedBall y₀ ρ)
    (width α w : ℝ) (I₁ I₂ : Finset ProfileScheduleTest) {L₁ L₂ : ℕ}
    (hL₁ : ∀ test ∈ I₁, test.length ≤ L₁)
    (hL₂ : ∀ test ∈ I₂, test.length ≤ L₂)
    (hc₁ : I₁.card ≤ N ^ 2 + 1) (hc₂ : I₂.card ≤ N ^ 2 + 1)
    (hL₁N : L₁ ≤ N) (hL₂N : L₂ ≤ N) {r : ℝ} (hr : 0 < r)
    (hdir : ∀ x ∈ X, ∀ y ∈ Y, pairDirection x y ∈ closedDirectionArc α (1 / 40))
    (hw : 10 * (tolerance θ N * N) ≤ w)
    (hlength₁ : 2 * (L₁ : ℝ) ≤ w + tolerance θ N * N)
    (hlength₂ : 2 * (L₂ : ℝ) ≤ w + tolerance θ N * N)
    (hΛ : ∀ x ∈ X, ∀ y ∈ Y, (2 : ℝ) ^ (w - 4) ≤ r * dist x y)
    (hterminal : ∀ x ∈ X, ∀ y ∈ Y, (2 : ℝ) ^ (-(N : ℝ) - 4) ≤ dist x y) :
    ‖angularScalarFourier (filteredCrossDistanceMeasure (ρ₁.restrict X) (ρ₂.restrict Y)
        (directionalPairMask
          (ScheduledSymbolData.maskProduct.symbol ρ₁ (tolerance θ N * N) width
            (8 * expansionCount θ N) I₁)
          (ScheduledSymbolData.maskProduct.symbol ρ₂ (tolerance θ N * N) width
            (8 * expansionCount θ N) I₂))) r -
      preparedCircleInversionConstant * (Real.sqrt r : ℂ) *
        ∫ z, preparedInverseCircleKernelSeries (expansionCount θ N) α
          (builtSymbolPairAngularAmplitude
            (ScheduledSymbolData.maskProduct.symbol ρ₁ (tolerance θ N * N) width
              (8 * expansionCount θ N) I₁)
            (ScheduledSymbolData.maskProduct.symbol ρ₂ (tolerance θ N * N) width
              (8 * expansionCount θ N) I₂) z.1 z.2) (z.1 - z.2) r
            ∂(ρ₁.restrict X).prod (ρ₂.restrict Y)‖ ≤
      (2 : ℝ) ^ (-(200 * (N : ℝ))) * (ρ₁.real X * ρ₂.real Y) := by
  let T := expansionCount θ N
  let E := tolerance θ N * N
  let b₁ := ScheduledSymbolData.maskProduct.symbol ρ₁ E width (8 * T) I₁
  let b₂ := ScheduledSymbolData.maskProduct.symbol ρ₂ E width (8 * T) I₂
  have hb₁ : Measurable (uncurry b₁) :=
    ScheduledSymbolData.maskProduct.measurable_symbol ρ₁ E width (8 * T) I₁
  have hb₂ : Measurable (uncurry b₂) :=
    ScheduledSymbolData.maskProduct.measurable_symbol ρ₂ E width (8 * T) I₂
  have hbound₁ (x w) : b₁ x w ∈ Set.Icc 0 1 := by
    rw [show b₁ = scheduledWidthMaskProduct ρ₁ E width (8 * T) I₁ from
      ScheduledSymbolData.maskProduct_symbol ρ₁ E width (8 * T) I₁]
    exact scheduledWidthMaskProduct_mem_Icc _ _ _ _ _ _ _
  have hbound₂ (x w) : b₂ x w ∈ Set.Icc 0 1 := by
    rw [show b₂ = scheduledWidthMaskProduct ρ₂ E width (8 * T) I₂ from
      ScheduledSymbolData.maskProduct_symbol ρ₂ E width (8 * T) I₂]
    exact scheduledWidthMaskProduct_mem_Icc _ _ _ _ _ _ _
  have hd : 0 < (2 : ℝ) ^ (-(N : ℝ) - 4) := by positivity
  have hf := integrable_maskedDistancePairFourierIntegrand ρ₁ ρ₂ hX hY hd hterminal
    hb₁ hb₂
    (fun x w ↦ abs_le.mpr ⟨by linarith [(hbound₁ x w).1], (hbound₁ x w).2⟩)
    (fun x w ↦ abs_le.mpr ⟨by linarith [(hbound₂ x w).1], (hbound₂ x w).2⟩) r
  have hg := (integrable_spatial_preparedInverseCircleKernelSeries T α .maskProduct .maskProduct
    ρ₁ ρ₂ hρ hsep hX hY hXball hYball E width (8 * T) I₁ I₂
    (by simp only [ScheduledSymbolData.maskProduct_order]; omega)
    (by simp only [ScheduledSymbolData.maskProduct_order]; omega) r).const_mul
    (preparedCircleInversionConstant * (Real.sqrt r : ℂ))
  have herr := norm_integral_sub_le_const hf hg (ε := (2 : ℝ) ^ (-(200 * (N : ℝ)))) (by
    filter_upwards [ae_restricted_product_carriers ρ₁ ρ₂ hX hY] with z hz
    have hs := builtSymbolPair_circle_mattila_inversion hpar hL₁ hL₂ hc₁ hc₂ hL₁N hL₂N
      (show b₁ ∈ scheduledSymbolClass ρ₁ E width (8 * T) I₁ (2 * T) from
        ⟨.maskProduct, by simp [ScheduledSymbolData.maskProduct_order], rfl⟩)
      (show b₂ ∈ scheduledSymbolClass ρ₂ E width (8 * T) I₂ (2 * T) from
        ⟨.maskProduct, by simp [ScheduledSymbolData.maskProduct_order], rfl⟩)
      (dist_pos.mp (hd.trans_le (hterminal _ hz.1 _ hz.2))) hr (hdir _ hz.1 _ hz.2)
      hw hlength₁ hlength₂ (by simpa only [dist_eq_norm] using hΛ _ hz.1 _ hz.2)
      (by simpa only [dist_eq_norm] using hterminal _ hz.1 _ hz.2)
    have he : maskedDistancePairFourierIntegrand b₁ b₂ r z =
        (Real.sqrt ‖z.1 - z.2‖ : ℂ)⁻¹ *
          Complex.exp (-((r * ‖z.1 - z.2‖ : ℝ) : ℂ) * Complex.I) *
          (b₁ z.1 (pairDirection z.1 z.2) * b₂ z.2 (pairDirection z.1 z.2) : ℝ) := by
      simp only [maskedDistancePairFourierIntegrand, directionalPairMask,
        ← dist_eq_norm, Complex.ofReal_inv]
      ring
    rw [he]
    exact hs)
  rw [integral_const_mul] at herr
  rw [← angularScalarFourier_maskedDistance_eq_integral ρ₁ ρ₂ hX hY hd hterminal
    hb₁ hb₂ hbound₁ hbound₂ r] at herr
  have hm : ((ρ₁.restrict X).prod (ρ₂.restrict Y)).real univ =
      ρ₁.real X * ρ₂.real Y := by
    simp only [Measure.real, ← Set.univ_prod_univ, Measure.prod_prod,
      Measure.restrict_apply_univ, ENNReal.toReal_mul]
  rw [hm] at herr
  exact herr

end FalconerThetaGauge
