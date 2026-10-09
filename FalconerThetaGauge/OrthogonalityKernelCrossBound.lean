module

public import FalconerThetaGauge.OrthogonalityKernelCrossFubini

/-! # Actual unlinked Fourier cross integrals retain all four true cell masses -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function

namespace FalconerThetaGauge

open GaugeFrostman

theorem ae_mem_four_carriers (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁]
    [IsFiniteMeasure ρ₂] {X X' Y Y' : Set Plane} (hX : MeasurableSet X)
    (hX' : MeasurableSet X') (hY : MeasurableSet Y) (hY' : MeasurableSet Y') :
    ∀ᵐ p : (Plane × Plane) × (Plane × Plane)
      ∂((ρ₁.restrict X).prod (ρ₁.restrict X')).prod ((ρ₂.restrict Y).prod (ρ₂.restrict Y')),
      p ∈ (X ×ˢ X') ×ˢ (Y ×ˢ Y') := by
  have h₁ : ∀ᵐ p ∂(ρ₁.restrict X).prod (ρ₁.restrict X'), p ∈ X ×ˢ X' := by
    apply (Measure.ae_prod_mem_iff_ae_ae_mem (hX.prod hX')).mpr
    filter_upwards [ae_restrict_mem hX] with x hx
    filter_upwards [ae_restrict_mem hX'] with x' hx'
    exact ⟨hx, hx'⟩
  have h₂ : ∀ᵐ p ∂(ρ₂.restrict Y).prod (ρ₂.restrict Y'), p ∈ Y ×ˢ Y' := by
    apply (Measure.ae_prod_mem_iff_ae_ae_mem (hY.prod hY')).mpr
    filter_upwards [ae_restrict_mem hY] with y hy
    filter_upwards [ae_restrict_mem hY'] with y' hy'
    exact ⟨hy, hy'⟩
  apply (Measure.ae_prod_mem_iff_ae_ae_mem ((hX.prod hX').prod (hY.prod hY'))).mpr
  filter_upwards [h₁] with p hp
  filter_upwards [h₂] with q hq
  exact ⟨hp, hq⟩

theorem norm_integral_maskedFourierArcPair_cross_unlinked {ρ : Measure Plane}
    [IsFiniteMeasure ρ] {θ : ℝ} {N a p v : ℕ}
    (hpar : ParameterFacts θ N) (hv : v ≤ N) (hpv : p ≤ v)
    (hw : 10 * (tolerance θ N * N) ≤ (v : ℝ) - p)
    (hgap : (p : ℝ) - a ≤ (v : ℝ) - p + 2 * (tolerance θ N * N))
    {width : ℝ} {I : Finset ProfileScheduleTest} {L : ℕ}
    (hcard : I.card ≤ N ^ 2 + 1) (hL : ∀ test ∈ I, test.length ≤ L)
    (hlength : (L : ℝ) ≤ (v : ℝ) - p + 2 * (tolerance θ N * N))
    {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ (tolerance θ N * N) width
      (8 * expansionCount θ N) I (2 * expansionCount θ N))
    (hb₂ : b₂ ∈ scheduledSymbolClass ρ (tolerance θ N * N) width
      (8 * expansionCount θ N) I (2 * expansionCount θ N))
    {X Y P P' Q Q' : Fin 2 → ℤ}
    (hP : dyadicCube p P ⊆ dyadicCube a X) (hP' : dyadicCube p P' ⊆ dyadicCube a X)
    (hQ : dyadicCube p Q ⊆ dyadicCube a Y) (hQ' : dyadicCube p Q' ⊆ dyadicCube a Y)
    (i j : Fin (angularPartitionCount (orthogonalityArcScale a p (tolerance θ N * N))))
    (hnot : ¬orthogonalityLinked p (orthogonalityLinkThreshold p (tolerance θ N * N))
      (unitCircleOfAngle (equalAngularCellCenter _ i))
      (unitCircleOfAngle (equalAngularCellCenter _ j)) (P, Q) (P', Q')) :
    ‖∫ z, maskedFourierArcPairAmplitude ρ ρ (dyadicCube p P) (dyadicCube p Q) b₁ b₂
      (8 * expansionCount θ N) (orthogonalityArcScale a p (tolerance θ N * N)) i j z *
      star (maskedFourierArcPairAmplitude ρ ρ (dyadicCube p P') (dyadicCube p Q') b₁ b₂
        (8 * expansionCount θ N) (orthogonalityArcScale a p (tolerance θ N * N)) i j z)
      ∂maskedFourierJointMeasure (8 * expansionCount θ N) v‖ ≤
        (64 * (4 : ℝ) ^ v * (2 * orthogonalityArcScale a p (tolerance θ N * N)) ^ 2 *
          (2 : ℝ) ^ (-(90 * (N : ℝ)))) *
        ((ρ.real (dyadicCube p P) * ρ.real (dyadicCube p P')) *
          (ρ.real (dyadicCube p Q) * ρ.real (dyadicCube p Q'))) := by
  rw [integral_maskedFourierArcPair_cross_eq_spatial ρ ρ _ _ _ _ _ _
    (orthogonalityArcScale_pos _ _ _) i j
    (measurable_of_mem_scheduledSymbolClass _ _ _ _ _ _ hb₁)
    (measurable_of_mem_scheduledSymbolClass _ _ _ _ _ _ hb₂)
    (abs_le_one_of_mem_scheduledSymbolClass _ _ _ _ _ (by omega) hb₁)
    (abs_le_one_of_mem_scheduledSymbolClass _ _ _ _ _ (by omega) hb₂)]
  have hae := ae_mem_four_carriers ρ ρ (measurableSet_dyadicCube p P)
    (measurableSet_dyadicCube p P') (measurableSet_dyadicCube p Q)
    (measurableSet_dyadicCube p Q')
  have hbound : ∀ᵐ z : (Plane × Plane) × (Plane × Plane)
      ∂((ρ.restrict (dyadicCube p P)).prod (ρ.restrict (dyadicCube p P'))).prod
        ((ρ.restrict (dyadicCube p Q)).prod (ρ.restrict (dyadicCube p Q'))),
      ‖orthogonalityTwoPairKernel (8 * expansionCount θ N) v
        (orthogonalityArcScale a p (tolerance θ N * N)) i j b₁ b₂ z.1.1 z.1.2 z.2.1 z.2.2‖ ≤
      64 * (4 : ℝ) ^ v * (2 * orthogonalityArcScale a p (tolerance θ N * N)) ^ 2 *
        (2 : ℝ) ^ (-(90 * (N : ℝ))) := by
    filter_upwards [hae] with z hz
    exact norm_orthogonalityTwoPairKernel_unlinked hpar hv hpv hw hgap hcard hL hlength
      hb₁ hb₂ hP hP' hQ hQ' hz.1.1 hz.1.2 hz.2.1 hz.2.2 i j hnot
  have hh := norm_integral_le_of_norm_le_const hbound
  have hm (μ ν : Measure (Plane × Plane)) [SFinite ν] :
      (μ.prod ν).real univ = μ.real univ * ν.real univ := by
    simpa only [univ_prod_univ] using measureReal_prod_prod (μ := μ) (ν := ν) univ univ
  have hm' (μ ν : Measure Plane) [SFinite ν] :
      (μ.prod ν).real univ = μ.real univ * ν.real univ := by
    simpa only [univ_prod_univ] using measureReal_prod_prod (μ := μ) (ν := ν) univ univ
  simp only [hm, hm'] at hh
  simpa only [Measure.real, Measure.restrict_apply_univ] using hh

theorem integrable_complex_cross_of_memLp_two {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x ↦ f x * star (g x)) μ := by
  apply (hf.norm.integrable_mul hg.norm).mono
  · exact hf.aestronglyMeasurable.mul hg.aestronglyMeasurable.star
  · filter_upwards [] with x
    simp only [norm_mul, norm_star, Pi.mul_apply, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), le_refl]

theorem abs_integral_real_inner_le_norm_complex_cross {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, inner ℝ (f x) (g x) ∂μ| ≤ ‖∫ x, f x * star (g x) ∂μ‖ := by
  have he (x : α) : inner ℝ (f x) (g x) = (f x * star (g x)).re := by
    rw [← real_inner_comm (f x) (g x)]
    exact Complex.inner (g x) (f x)
  simp_rw [he]
  change |∫ x, RCLike.re (f x * star (g x)) ∂μ| ≤ _
  rw [integral_re (integrable_complex_cross_of_memLp_two hf hg)]
  exact Complex.abs_re_le_norm _

theorem abs_integral_real_inner_maskedFourierArcPair_unlinked {ρ : Measure Plane}
    [IsFiniteMeasure ρ] {θ : ℝ} {N a p v : ℕ}
    (hpar : ParameterFacts θ N) (hv : v ≤ N) (hpv : p ≤ v)
    (hw : 10 * (tolerance θ N * N) ≤ (v : ℝ) - p)
    (hgap : (p : ℝ) - a ≤ (v : ℝ) - p + 2 * (tolerance θ N * N))
    {width : ℝ} {I : Finset ProfileScheduleTest} {L : ℕ}
    (hcard : I.card ≤ N ^ 2 + 1) (hL : ∀ test ∈ I, test.length ≤ L)
    (hlength : (L : ℝ) ≤ (v : ℝ) - p + 2 * (tolerance θ N * N))
    {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ (tolerance θ N * N) width
      (8 * expansionCount θ N) I (2 * expansionCount θ N))
    (hb₂ : b₂ ∈ scheduledSymbolClass ρ (tolerance θ N * N) width
      (8 * expansionCount θ N) I (2 * expansionCount θ N))
    {X Y P P' Q Q' : Fin 2 → ℤ}
    (hP : dyadicCube p P ⊆ dyadicCube a X) (hP' : dyadicCube p P' ⊆ dyadicCube a X)
    (hQ : dyadicCube p Q ⊆ dyadicCube a Y) (hQ' : dyadicCube p Q' ⊆ dyadicCube a Y)
    (i j : Fin (angularPartitionCount (orthogonalityArcScale a p (tolerance θ N * N))))
    (hnot : ¬orthogonalityLinked p (orthogonalityLinkThreshold p (tolerance θ N * N))
      (unitCircleOfAngle (equalAngularCellCenter _ i))
      (unitCircleOfAngle (equalAngularCellCenter _ j)) (P, Q) (P', Q')) :
    |∫ z, inner ℝ
      (maskedFourierArcPairAmplitude ρ ρ (dyadicCube p P) (dyadicCube p Q) b₁ b₂
        (8 * expansionCount θ N) (orthogonalityArcScale a p (tolerance θ N * N)) i j z)
      (maskedFourierArcPairAmplitude ρ ρ (dyadicCube p P') (dyadicCube p Q') b₁ b₂
        (8 * expansionCount θ N) (orthogonalityArcScale a p (tolerance θ N * N)) i j z)
      ∂maskedFourierJointMeasure (8 * expansionCount θ N) v| ≤
        (64 * (4 : ℝ) ^ v * (2 * orthogonalityArcScale a p (tolerance θ N * N)) ^ 2 *
          (2 : ℝ) ^ (-(90 * (N : ℝ)))) *
        ((ρ.real (dyadicCube p P) * ρ.real (dyadicCube p P')) *
          (ρ.real (dyadicCube p Q) * ρ.real (dyadicCube p Q'))) := by
  have hm₁ := measurable_of_mem_scheduledSymbolClass _ _ _ _ _ _ hb₁
  have hm₂ := measurable_of_mem_scheduledSymbolClass _ _ _ _ _ _ hb₂
  have hd₁ := abs_le_one_of_mem_scheduledSymbolClass _ _ _ _ _ (by omega) hb₁
  have hd₂ := abs_le_one_of_mem_scheduledSymbolClass _ _ _ _ _ (by omega) hb₂
  have hf := memLp_maskedFourierArcPairAmplitude ρ ρ (dyadicCube p P) (dyadicCube p Q)
    hm₁ hm₂ hd₁ hd₂ (8 * expansionCount θ N) v (orthogonalityArcScale_pos _ _ _) i j
  have hg := memLp_maskedFourierArcPairAmplitude ρ ρ (dyadicCube p P') (dyadicCube p Q')
    hm₁ hm₂ hd₁ hd₂ (8 * expansionCount θ N) v (orthogonalityArcScale_pos _ _ _) i j
  exact (abs_integral_real_inner_le_norm_complex_cross hf hg).trans
    (norm_integral_maskedFourierArcPair_cross_unlinked hpar hv hpv hw hgap hcard hL hlength
      hb₁ hb₂ hP hP' hQ hQ' i j hnot)

end FalconerThetaGauge
