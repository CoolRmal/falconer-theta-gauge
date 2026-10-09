module

public import FalconerThetaGauge.RadialProjectionLine
public import FalconerThetaGauge.OrliczDuality

/-!
# Extended Orlicz transfer for actual radial densities

The extended functions agree with the manuscript's real functions on finite
nonnegative arguments and take the value infinity at infinity. This preserves
monotonicity when a positive-ray density is not yet known finite. The radial
transfer then applies directly to the literal circle pushforward densities.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace FalconerThetaGauge

/-- The genuine extended version of `t log(exp(1)+t)^γ`. -/
def orliczPhiExtended (γ : ℝ) (t : ℝ≥0∞) : ℝ≥0∞ :=
  if t = ∞ then ∞ else orliczPhiENN γ t.toReal

/-- The genuine extended version of `t² log(exp(1)+t)^γ`. -/
def orliczQuadraticExtended (γ : ℝ) (t : ℝ≥0∞) : ℝ≥0∞ :=
  if t = ∞ then ∞ else orliczQuadraticENN γ t.toReal

@[simp]
theorem orliczPhiExtended_top (γ : ℝ) : orliczPhiExtended γ ∞ = ∞ := by
  simp [orliczPhiExtended]

@[simp]
theorem orliczQuadraticExtended_top (γ : ℝ) : orliczQuadraticExtended γ ∞ = ∞ := by
  simp [orliczQuadraticExtended]

@[simp]
theorem orliczPhiExtended_ofReal (γ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    orliczPhiExtended γ (ENNReal.ofReal t) = orliczPhiENN γ t := by
  simp [orliczPhiExtended, ENNReal.toReal_ofReal ht]

@[simp]
theorem orliczQuadraticExtended_ofReal (γ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    orliczQuadraticExtended γ (ENNReal.ofReal t) = orliczQuadraticENN γ t := by
  simp [orliczQuadraticExtended, ENNReal.toReal_ofReal ht]

@[fun_prop]
theorem measurable_orliczPhiExtended (γ : ℝ) : Measurable (orliczPhiExtended γ) := by
  unfold orliczPhiExtended orliczPhiENN orliczPhi
  exact Measurable.ite (measurableSet_singleton ∞) measurable_const (by fun_prop)

@[fun_prop]
theorem measurable_orliczQuadraticExtended (γ : ℝ) :
    Measurable (orliczQuadraticExtended γ) := by
  unfold orliczQuadraticExtended orliczQuadraticENN orliczQuadratic
  exact Measurable.ite (measurableSet_singleton ∞) measurable_const (by fun_prop)

theorem monotone_orliczPhiExtended {γ : ℝ} (hγ : 0 ≤ γ) : Monotone (orliczPhiExtended γ) := by
  intro a b hab
  by_cases hb : b = ∞
  · simp [hb]
  have ha : a ≠ ∞ := ne_top_of_le_ne_top hb hab
  simp only [orliczPhiExtended, ite_eq_right ha, ite_eq_right hb, orliczPhiENN]
  exact ENNReal.ofReal_le_ofReal
    (orliczPhi_mono hγ ENNReal.toReal_nonneg ((ENNReal.toReal_le_toReal ha hb).mpr hab))

/-- The manuscript's elementary product inequality, also valid at infinite arguments. -/
theorem orliczExtended_product_le {γ : ℝ} (hγ : 0 ≤ γ) (a b : ℝ≥0∞) :
    orliczPhiExtended γ a * b ≤ orliczQuadraticExtended γ a +
      orliczQuadraticExtended γ b := by
  by_cases ha : a = ∞
  · simp [ha]
  by_cases hb : b = ∞
  · simp [hb]
  simp only [orliczPhiExtended, orliczQuadraticExtended,
    ite_eq_right ha, ite_eq_right hb, orliczPhiENN, orliczQuadraticENN]
  conv_lhs => rw [← ENNReal.ofReal_toReal hb]
  rw [← ENNReal.ofReal_mul (orliczPhi_nonneg γ ENNReal.toReal_nonneg),
    ← ENNReal.ofReal_add (orliczQuadratic_nonneg γ ENNReal.toReal_nonneg)
      (orliczQuadratic_nonneg γ ENNReal.toReal_nonneg)]
  exact ENNReal.ofReal_le_ofReal
    (orlicz_product_le hγ ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

/-- Removing the bounded distance weight costs the explicit factor from Theorem 5.4. -/
theorem orliczPhiExtended_mul_le {γ D : ℝ} (hγ : 0 ≤ γ) (hD : 1 ≤ D) (t : ℝ≥0∞) :
    orliczPhiExtended γ (ENNReal.ofReal D * t) ≤
      ENNReal.ofReal (D * (1 + Real.log D) ^ γ) * orliczPhiExtended γ t := by
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hlog : 0 ≤ Real.log D := Real.log_nonneg hD
  have hcost : 0 < D * (1 + Real.log D) ^ γ :=
    mul_pos hDpos (Real.rpow_pos_of_pos (by linarith) γ)
  by_cases ht : t = ∞
  · simp [ht, ENNReal.mul_top, (ENNReal.ofReal_pos.mpr hDpos).ne',
      (ENNReal.ofReal_pos.mpr hcost).ne']
  have hprod : ENNReal.ofReal D * t ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ht
  simp only [orliczPhiExtended, ite_eq_right ht, ite_eq_right hprod, orliczPhiENN,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hDpos.le]
  rw [← ENNReal.ofReal_mul hcost.le]
  exact ENNReal.ofReal_le_ofReal (orliczPhi_mul_le hγ hD ENNReal.toReal_nonneg)

/-- The elementary Orlicz transfer is a genuine integral inequality against a density. -/
theorem lintegral_orliczPhiExtended_withDensity_le {α : Type*} [MeasurableSpace α]
    (ξ : Measure α) {a b : α → ℝ≥0∞} (ha : Measurable a) (hb : Measurable b)
    {γ : ℝ} (hγ : 0 ≤ γ) :
    (∫⁻ x, orliczPhiExtended γ (a x) ∂ξ.withDensity b) ≤
      (∫⁻ x, orliczQuadraticExtended γ (a x) ∂ξ) +
        ∫⁻ x, orliczQuadraticExtended γ (b x) ∂ξ := by
  rw [lintegral_withDensity_eq_lintegral_mul ξ hb
    (g := fun x ↦ orliczPhiExtended γ (a x)) (by fun_prop),
    ← lintegral_add_left (f := fun x ↦ orliczQuadraticExtended γ (a x))
      (by fun_prop) (fun x ↦ orliczQuadraticExtended γ (b x))]
  apply lintegral_mono
  intro x
  dsimp only [Pi.mul_apply]
  rw [mul_comm]
  exact orliczExtended_product_le hγ (a x) (b x)

/-- The actual smoothed radial Orlicz integral transfers to orthogonal line densities,
with the precise factor for removing the bounded inverse-distance weight. -/
theorem lintegral_circleRayDensity_orlicz_le_orthogonal {f : Plane → ℝ≥0∞}
    (hf : Measurable f) (ν : Measure Plane) [SFinite ν] {γ D : ℝ}
    (hγ : 0 ≤ γ) (hD : 1 ≤ D)
    (hDdist : ∀ᵐ x ∂ν, ∀ y, f y ≠ 0 → dist x y ≤ D) :
    (∫⁻ x, ∫⁻ w, orliczPhiExtended γ (circleRayDensity f x w) ∂circleArcLength ∂ν) ≤
      ENNReal.ofReal (D * (1 + Real.log D) ^ γ) *
        ∫⁻ θ, ∫⁻ t : ℝ,
          orliczPhiExtended γ
            (orthogonalLineDensity (angularCartesianFrame (θ - Real.pi / 2)) f t)
            ∂ν.map (fun x ↦ ⟪x, angularDirection (θ - Real.pi / 2)⟫)
          ∂radialAngularMeasure := by
  refine (lintegral_circleRayDensity_comp_le_orthogonal hf ν hDdist
    (measurable_orliczPhiExtended γ) (monotone_orliczPhiExtended hγ)).trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro θ
  dsimp only
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_mono fun t ↦ orliczPhiExtended_mul_le hγ hD _

end FalconerThetaGauge
