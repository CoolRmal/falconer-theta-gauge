module

public import FalconerThetaGauge.OrthogonalityLinks
public import FalconerThetaGauge.EqualArcCutoffRegularity
public import FalconerThetaGauge.MaskedMattilaSymbolScale

/-! # Actual angular amplitudes and their source orthogonality derivative budget -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff

namespace FalconerThetaGauge

open GaugeFrostman

theorem orthogonalityArcScale_eq_rpow (a p : ℕ) (E : ℝ) :
    orthogonalityArcScale a p E = min 1 ((2 : ℝ) ^ ((a : ℝ) - p + E)) := by
  rw [orthogonalityArcScale, dyadicRadius, dyadicRadius,
    ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 2
  ring

theorem orthogonalityArcScale_inv_le_frequency {a p v : ℕ} {E : ℝ} (hpv : p ≤ v)
    (hE : 0 ≤ E) (hgap : (p : ℝ) - a ≤ (v : ℝ) - p + 2 * E) :
    1 / orthogonalityArcScale a p E ≤ (2 : ℝ) ^ ((v : ℝ) - p + E) := by
  have hpv' : (p : ℝ) ≤ v := by exact_mod_cast hpv
  have hF : 1 ≤ (2 : ℝ) ^ ((v : ℝ) - p + E) :=
    Real.one_le_rpow (by norm_num) (by linarith)
  rw [orthogonalityArcScale_eq_rpow]
  by_cases hs : (2 : ℝ) ^ ((a : ℝ) - p + E) ≤ 1
  · rw [min_eq_right hs, one_div, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  · simpa only [min_eq_left (le_of_not_ge hs), div_one] using hF

theorem scheduled_mask_orthogonality_factor_le {p v L : ℕ} {E : ℝ}
    (hpv : p ≤ v) (_hE : 0 ≤ E) (hL : (L : ℝ) ≤ (v : ℝ) - p + 2 * E) :
    max 1 ((2 : ℝ) ^ (L : ℝ) * (2 : ℝ) ^ (-E)) ≤
      (2 : ℝ) ^ ((v : ℝ) - p + E) := by
  apply max_le
  · apply Real.one_le_rpow (by norm_num)
    have hpv' : (p : ℝ) ≤ v := by exact_mod_cast hpv
    linarith
  · rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

def orthogonalityAngularScale (T : ℕ) (E : ℝ) (I : Finset ProfileScheduleTest)
    (L a p : ℕ) : ℝ :=
  576 * (T : ℝ) ^ 2 / orthogonalityArcScale a p E +
    2 * max 1 (scheduledSymbolScale T E I L)

def orthogonalityAngularAmplitude (K : ℕ) (ℓ : ℝ)
    (arc : Fin (angularPartitionCount ℓ)) (b : Plane → UnitCircle → ℝ)
    (x x' : Plane) : ℝ → ℂ := fun θ ↦
  (equalArcCutoff K ℓ arc (unitCircleOfAngle θ) : ℂ) *
    builtSymbolPairAngularAmplitude b b x x' θ

theorem orthogonalityAngularAmplitude_isDerivativeRegular {ρ : Measure Plane}
    {T : ℕ} (hT : 1 ≤ T) {E width : ℝ} {I : Finset ProfileScheduleTest} {L a p : ℕ}
    (hL : ∀ test ∈ I, test.length ≤ L) {b : Plane → UnitCircle → ℝ}
    (hb : b ∈ scheduledSymbolClass ρ E width (8 * T) I (2 * T))
    (arc : Fin (angularPartitionCount (orthogonalityArcScale a p E))) (x x' : Plane) :
    IsDerivativeRegular 1 (orthogonalityAngularScale T E I L a p) (6 * T)
      (orthogonalityAngularAmplitude (8 * T) (orthogonalityArcScale a p E) arc b x x') := by
  have hχ := equalArcCutoff_isDerivativeRegular_of_order hT (by omega : 6 * T ≤ 8 * T)
    (orthogonalityArcScale_pos a p E) (orthogonalityArcScale_le_one a p E) arc
  have hbreg := builtSymbolPairAngularAmplitude_isDerivativeRegular hL hL hb hb x x'
  have hfun : orthogonalityAngularAmplitude (8 * T) (orthogonalityArcScale a p E) arc b x x' =
      (fun θ ↦ (equalArcCutoff (8 * T) (orthogonalityArcScale a p E) arc
        (unitCircleOfAngle θ) : ℂ)) * builtSymbolPairAngularAmplitude b b x x' := rfl
  rw [hfun]
  simpa only [orthogonalityAngularScale, one_mul, two_mul] using hχ.mul hbreg

theorem orthogonalityAngularScale_le_frequency {T N a p v : ℕ} (hT : 1 ≤ T)
    {E : ℝ} (hE : 0 ≤ E) (hpv : p ≤ v)
    (hgap : (p : ℝ) - a ≤ (v : ℝ) - p + 2 * E)
    (I : Finset ProfileScheduleTest) {L : ℕ} (hcard : I.card ≤ N ^ 2 + 1)
    (hL : (L : ℝ) ≤ (v : ℝ) - p + 2 * E) :
    orthogonalityAngularScale T E I L a p ≤
      1024 * (T : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1) * (2 : ℝ) ^ ((v : ℝ) - p + E) := by
  have hpv' : (p : ℝ) ≤ v := by exact_mod_cast hpv
  have hF : 1 ≤ (2 : ℝ) ^ ((v : ℝ) - p + E) :=
    Real.one_le_rpow (by norm_num) (by linarith)
  have hm := scheduledSymbolScale_max_one_le hT N E I L hcard hF
    (scheduled_mask_orthogonality_factor_le hpv hE hL)
  have hc : 576 * (T : ℝ) ^ 2 / orthogonalityArcScale a p E ≤
      576 * (T : ℝ) ^ 2 * (2 : ℝ) ^ ((v : ℝ) - p + E) := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
      (orthogonalityArcScale_inv_le_frequency hpv hE hgap)
      (by positivity : 0 ≤ 576 * (T : ℝ) ^ 2)
  unfold orthogonalityAngularScale
  have hnonneg : 0 ≤ (T : ℝ) ^ 2 * (2 : ℝ) ^ ((v : ℝ) - p + E) := by positivity
  have hn := mul_nonneg (sq_nonneg (N : ℝ)) hnonneg
  nlinarith

end FalconerThetaGauge
