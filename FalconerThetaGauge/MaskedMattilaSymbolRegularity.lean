module

public import FalconerThetaGauge.MaskedMattilaPointwiseInversion
public import FalconerThetaGauge.ScheduledSymbolBudget

/-! # Genuine built-symbol amplitudes for the pointwise masked Mattila inversion -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff

namespace FalconerThetaGauge

def builtSymbolAngularAmplitude (b : Plane → UnitCircle → ℝ) (x : Plane) : ℝ → ℂ :=
  fun θ ↦ (b x (unitCircleOfAngle θ) : ℂ)

def builtSymbolPairAngularAmplitude (b₁ b₂ : Plane → UnitCircle → ℝ)
    (x y : Plane) : ℝ → ℂ := builtSymbolAngularAmplitude b₁ x * builtSymbolAngularAmplitude b₂ y

theorem contDiff_builtSymbolAngularAmplitude {ρ : Measure Plane} {E width : ℝ}
    {K k₀ : ℕ} {I : Finset ProfileScheduleTest} {b : Plane → UnitCircle → ℝ}
    (hb : b ∈ scheduledSymbolClass ρ E width K I k₀) (x : Plane) :
    ContDiff ℝ ∞ (builtSymbolAngularAmplitude b x) := by
  obtain ⟨d, horder, rfl⟩ := hb
  exact Complex.ofRealCLM.contDiff.comp (d.contDiff_symbol_comp_angle ρ E width K I x)

/-- Empty test lists are included: `max 1 M_L` supplies the scale lower bound,
while every derivative estimate follows from the actual Leibniz expansion. -/
theorem builtSymbolAngularAmplitude_isDerivativeRegular {ρ : Measure Plane} {T : ℕ}
    {E width : ℝ} {I : Finset ProfileScheduleTest} {L : ℕ}
    (hL : ∀ test ∈ I, test.length ≤ L) {b : Plane → UnitCircle → ℝ}
    (hb : b ∈ scheduledSymbolClass ρ E width (8 * T) I (2 * T)) (x : Plane) :
    IsDerivativeRegular 1 (max 1 (scheduledSymbolScale T E I L)) (6 * T)
      (builtSymbolAngularAmplitude b x) := by
  obtain ⟨d, horder, rfl⟩ := hb
  have hf := d.contDiff_symbol_comp_angle ρ E width (8 * T) I x
  refine ⟨by norm_num, le_max_left _ _,
    (Complex.ofRealCLM.contDiff.comp hf).of_le
      (ENat.natCast_le_of_coe_top_le_withTop (le_refl ∞) (6 * T)), ?_⟩
  intro j hj θ
  change ‖iteratedDeriv j (fun t ↦ (d.symbol ρ E width (8 * T) I x
    (unitCircleOfAngle t) : ℂ)) θ‖ ≤ _
  rw [iteratedDeriv_ofReal_eq ((hf.of_le (by simp)).contDiffAt)]
  simp only [Complex.norm_real, Real.norm_eq_abs, one_mul]
  exact (d.abs_iteratedDeriv_symbol_le ρ E width I hL j (by omega) x θ).trans
    (pow_le_pow_left₀ (scheduledSymbolScale_nonneg _ _ _ _) (le_max_right _ _) j)

theorem builtSymbolPairAngularAmplitude_isDerivativeRegular {ρ₁ ρ₂ : Measure Plane}
    {T : ℕ} {E width : ℝ} {I₁ I₂ : Finset ProfileScheduleTest} {L₁ L₂ : ℕ}
    (hL₁ : ∀ test ∈ I₁, test.length ≤ L₁) (hL₂ : ∀ test ∈ I₂, test.length ≤ L₂)
    {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ₁ E width (8 * T) I₁ (2 * T))
    (hb₂ : b₂ ∈ scheduledSymbolClass ρ₂ E width (8 * T) I₂ (2 * T)) (x y : Plane) :
    IsDerivativeRegular 1 (max 1 (scheduledSymbolScale T E I₁ L₁) +
      max 1 (scheduledSymbolScale T E I₂ L₂)) (6 * T)
      (builtSymbolPairAngularAmplitude b₁ b₂ x y) := by
  simpa only [one_mul, builtSymbolPairAngularAmplitude] using
    (builtSymbolAngularAmplitude_isDerivativeRegular hL₁ hb₁ x).mul
      (builtSymbolAngularAmplitude_isDerivativeRegular hL₂ hb₂ y)

theorem periodic_builtSymbolAngularAmplitude (b : Plane → UnitCircle → ℝ) (x : Plane) :
    Periodic (builtSymbolAngularAmplitude b x) (2 * Real.pi) := by
  intro θ
  simp only [builtSymbolAngularAmplitude, unitCircleOfAngle_add_two_pi]

theorem periodic_builtSymbolPairAngularAmplitude (b₁ b₂ : Plane → UnitCircle → ℝ)
    (x y : Plane) : Periodic (builtSymbolPairAngularAmplitude b₁ b₂ x y) (2 * Real.pi) := by
  intro θ
  change builtSymbolAngularAmplitude b₁ x (θ + 2 * Real.pi) *
    builtSymbolAngularAmplitude b₂ y (θ + 2 * Real.pi) = _
  rw [periodic_builtSymbolAngularAmplitude, periodic_builtSymbolAngularAmplitude]
  rfl

theorem contDiff_builtSymbolPairAngularAmplitude {ρ₁ ρ₂ : Measure Plane}
    {E width : ℝ} {K k₀ : ℕ} {I₁ I₂ : Finset ProfileScheduleTest}
    {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ₁ E width K I₁ k₀)
    (hb₂ : b₂ ∈ scheduledSymbolClass ρ₂ E width K I₂ k₀) (x y : Plane) :
    ContDiff ℝ ∞ (builtSymbolPairAngularAmplitude b₁ b₂ x y) := by
  exact (contDiff_builtSymbolAngularAmplitude hb₁ x).mul
    (contDiff_builtSymbolAngularAmplitude hb₂ y)

end FalconerThetaGauge
