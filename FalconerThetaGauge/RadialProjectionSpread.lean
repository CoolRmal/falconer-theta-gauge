module

public import FalconerThetaGauge.RadialProjectionSpreadRestriction

/-!
# Uniform radial Orlicz spread on compact retained carriers

This is the radial spread part of the gauge preparation. Starting with only
positive gauge Hausdorff measure, Borel bounded good-pin sets yield actual
compact quarter-mass carriers. Normalizing both restrictions preserves the
geometry and gauge and gives a common finite eighth-order radial bound at
every retained carrier point in both directions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerThetaGauge

/-- Explicit eighth-order Orlicz cost of a quarter-mass source normalization. -/
def radialRestrictionOrliczConstant : ℝ := 4 * (1 + Real.log 4) ^ (8 : ℝ)

theorem radialRestrictionOrliczConstant_pos : 0 < radialRestrictionOrliczConstant := by
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (by linarith) _)

open GaugeSeparatedMeasures in
/-- Genuine uniform radial preparation on both compact supports. Every pin in
either retained carrier has the actual radial density and the common Φ₈ bound. -/
theorem exists_prepared_probabilityMeasures_uniform_radial_orlicz {θ : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1) {E : Set Plane} (hE : IsCompact E)
    (hGauge : 0 < gaugeMeasure θ E) :
    ∃ (ℓ C K : ℝ) (z a b : Plane) (S₁ S₂ : Set Plane)
      (μ₁ μ₂ : ProbabilityMeasure Plane),
      0 < ℓ ∧ 0 < C ∧ 0 < K ∧ IsCompact S₁ ∧ IsCompact S₂ ∧
      S₁ ⊆ affineMap ℓ z '' E ∧ S₂ ⊆ affineMap ℓ z '' E ∧
      (μ₁ : Measure Plane) S₁ = 1 ∧ (μ₂ : Measure Plane) S₂ = 1 ∧
      (μ₁ : Measure Plane).support ⊆ S₁ ∧ (μ₂ : Measure Plane).support ⊆ S₂ ∧
      dist a b = 1 / 4 ∧
      S₁ ⊆ Metric.ball a (1 / 400) ∧ S₂ ⊆ Metric.ball b (1 / 400) ∧
      Metric.ball a (1 / 400) ⊆ unitSquare ∧ Metric.ball b (1 / 400) ⊆ unitSquare ∧
      (∀ x ∈ S₁, ∀ y ∈ S₂,
        (24 / 100 : ℝ) ≤ dist x y ∧ dist x y ≤ (26 / 100 : ℝ)) ∧
      HasGaugeBallBound (μ₁ : Measure Plane) θ C ∧ HasGaugeBallBound (μ₂ : Measure Plane) θ C ∧
      (∀ γ : ℝ, 1 ≤ γ →
        logCriticalEnergy γ (μ₁ : Measure Plane) ≠ ∞ ∧
        logCriticalEnergy γ (μ₂ : Measure Plane) ≠ ∞) ∧
      (∀ x ∈ S₁,
        (μ₂ : Measure Plane).map (radialProjection x) ≪ circleArcLength ∧
        circleArcLength.withDensity (radialProjectionDensity (μ₂ : Measure Plane) x) =
          (μ₂ : Measure Plane).map (radialProjection x) ∧
        radialOrliczMoment (μ₂ : Measure Plane) 8 x ≤ ENNReal.ofReal K) ∧
      (∀ y ∈ S₂,
        (μ₁ : Measure Plane).map (radialProjection y) ≪ circleArcLength ∧
        circleArcLength.withDensity (radialProjectionDensity (μ₁ : Measure Plane) y) =
          (μ₁ : Measure Plane).map (radialProjection y) ∧
        radialOrliczMoment (μ₁ : Measure Plane) 8 y ≤ ENNReal.ofReal K) := by
  obtain ⟨ℓ, C, z, a, b, S₁, S₂, μ₁, μ₂, hℓ, hC, hS₁, hS₂, hsub₁, hsub₂,
    hmass₁, hmass₂, hsupp₁, hsupp₂, hab, hball₁, hball₂, hsq₁, hsq₂,
    hsep, hgb₁, hgb₂, henergy⟩ :=
    exists_prepared_probabilityMeasures_radial_orlicz hθ₀ hθ₁ hE hGauge
  have hgood₁ : ∀ᵐ x ∂(μ₁ : Measure Plane),
      μ₂.map (radialProjection x) ≪ circleArcLength ∧ radialOrliczMoment μ₂ 8 x ≠ ∞ := by
    filter_upwards [(henergy 8 (by norm_num)).2.2.2.2.1] with x hx
    exact ⟨hx.1, hx.2.2⟩
  have hgood₂ : ∀ᵐ y ∂(μ₂ : Measure Plane),
      μ₁.map (radialProjection y) ≪ circleArcLength ∧ radialOrliczMoment μ₁ 8 y ≠ ∞ := by
    filter_upwards [(henergy 8 (by norm_num)).2.2.2.2.2] with y hy
    exact ⟨hy.1, hy.2.2⟩
  obtain ⟨n₁, A₁, hA₁, hA₁sub, hμA₁, hgoodA₁⟩ :=
    exists_compact_goodRadialPins μ₁ μ₂ 8 hS₁ hmass₁ hgood₁
  obtain ⟨n₂, A₂, hA₂, hA₂sub, hμA₂, hgoodA₂⟩ :=
    exists_compact_goodRadialPins μ₂ μ₁ 8 hS₂ hmass₂ hgood₂
  let ν₁ := retainedRadialProbability μ₁ A₁ hμA₁.le
  let ν₂ := retainedRadialProbability μ₂ A₂ hμA₂.le
  let B : ℝ := max n₁ n₂ + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  have hn₁ : (n₁ : ℝ≥0∞) ≤ ENNReal.ofReal B := by
    rw [← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    have h : n₁ ≤ max n₁ n₂ := le_max_left _ _
    dsimp only [B]
    exact (by exact_mod_cast h : (n₁ : ℝ) ≤ max n₁ n₂).trans (by linarith)
  have hn₂ : (n₂ : ℝ≥0∞) ≤ ENNReal.ofReal B := by
    rw [← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    have h : n₂ ≤ max n₁ n₂ := le_max_right _ _
    dsimp only [B]
    exact (by exact_mod_cast h : (n₂ : ℝ) ≤ max n₁ n₂).trans (by linarith)
  have hgb₁' : HasGaugeBallBound (ν₁ : Measure Plane) θ (4 * C) :=
    hasGaugeBallBound_retainedRadialProbability μ₁ hμA₁.le hgb₁
  have hgb₂' : HasGaugeBallBound (ν₂ : Measure Plane) θ (4 * C) :=
    hasGaugeBallBound_retainedRadialProbability μ₂ hμA₂.le hgb₂
  have hν₁data := retainedRadialProbability_carrier μ₁ hA₁ hμA₁.le
  have hν₂data := retainedRadialProbability_carrier μ₂ hA₂ hμA₂.le
  refine ⟨ℓ, 4 * C, radialRestrictionOrliczConstant * B, z, a, b, A₁, A₂, ν₁, ν₂,
    hℓ, by positivity, mul_pos radialRestrictionOrliczConstant_pos hB, hA₁, hA₂,
    hA₁sub.trans hsub₁, hA₂sub.trans hsub₂, hν₁data.1, hν₂data.1, hν₁data.2, hν₂data.2,
    hab, hA₁sub.trans hball₁, hA₂sub.trans hball₂, hsq₁, hsq₂,
    fun x hx y hy ↦ hsep x (hA₁sub hx) y (hA₂sub hy), hgb₁', hgb₂', ?_, ?_, ?_⟩
  · intro γ hγ
    exact ⟨logCriticalEnergy_ne_top_of_hasGaugeBallBound hγ hθ₀ (by positivity) hgb₁',
      logCriticalEnergy_ne_top_of_hasGaugeBallBound hγ hθ₀ (by positivity) hgb₂'⟩
  · intro x hx
    have hbound := radialProjection_retained_density_bound μ₂ hμA₂.le x
      (hgoodA₁ x hx).1 (γ := 8) (by norm_num) ((hgoodA₁ x hx).2.trans hn₁)
    have hcost : 0 ≤ 4 * (1 + Real.log 4) ^ (8 : ℝ) := radialRestrictionOrliczConstant_pos.le
    rw [← ENNReal.ofReal_mul hcost] at hbound
    exact hbound
  · intro y hy
    have hbound := radialProjection_retained_density_bound μ₁ hμA₁.le y
      (hgoodA₂ y hy).1 (γ := 8) (by norm_num) ((hgoodA₂ y hy).2.trans hn₂)
    have hcost : 0 ≤ 4 * (1 + Real.log 4) ^ (8 : ℝ) := radialRestrictionOrliczConstant_pos.le
    rw [← ENNReal.ofReal_mul hcost] at hbound
    exact hbound

end FalconerThetaGauge
