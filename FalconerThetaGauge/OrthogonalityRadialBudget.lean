module

public import FalconerThetaGauge.OrthogonalityRadialDecay
public import FalconerThetaGauge.OrthogonalityLinks
public import FalconerThetaGauge.StationaryCircularInversionDecay

/-! # The literal radial cancellation is at most the source power `R⁻³⁰⁰` -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FalconerThetaGauge

theorem radialPolynomialBudget_le_sourceBudget (T N : ℕ) :
    1024 * (T : ℝ) ^ 2 ≤
      (2 : ℝ) ^ (80 : ℕ) * ((T : ℝ) + 1) ^ (12 : ℕ) *
        ((N : ℝ) + 16) ^ (12 : ℕ) := by
  have hT : (T : ℝ) ^ 2 ≤ ((T : ℝ) + 1) ^ 12 := by
    calc
      _ ≤ ((T : ℝ) + 1) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) 2
      _ ≤ _ := pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) T; linarith)
        (by norm_num : 2 ≤ 12)
  have hN : (1 : ℝ) ≤ ((N : ℝ) + 16) ^ 12 :=
    one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  calc
    _ ≤ (2 : ℝ) ^ (80 : ℕ) * ((T : ℝ) + 1) ^ (12 : ℕ) := by gcongr; norm_num
    _ ≤ _ := le_mul_of_one_le_right (by positivity) hN

theorem orthogonality_radial_ratio_le {T N p v : ℕ} {E : ℝ} (hE : 0 ≤ E)
    (hw : 10 * E ≤ (v : ℝ) - p)
    (hP1 : (2 : ℝ) ^ (80 : ℕ) * ((T : ℝ) + 1) ^ (12 : ℕ) *
      ((N : ℝ) + 16) ^ (12 : ℕ) ≤ (2 : ℝ) ^ (E / 8)) :
    1024 * (T : ℝ) ^ 2 / ((2 : ℝ) ^ v * orthogonalityLinkThreshold p E) ≤
      (2 : ℝ) ^ (-(11 * E)) := by
  have heq : (2 : ℝ) ^ v * orthogonalityLinkThreshold p E =
      (2 : ℝ) ^ ((v : ℝ) - p + 3 * E / 2) := by
    simp only [orthogonalityLinkThreshold, GaugeFrostman.dyadicRadius,
      ← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [heq]
  calc
    _ ≤ (2 : ℝ) ^ (E / 8) / (2 : ℝ) ^ ((v : ℝ) - p + 3 * E / 2) :=
      div_le_div_of_nonneg_right ((radialPolynomialBudget_le_sourceBudget T N).trans hP1)
        (by positivity)
    _ = (2 : ℝ) ^ (E / 8 - ((v : ℝ) - p + 3 * E / 2)) :=
      (Real.rpow_sub (by norm_num : (0 : ℝ) < 2) _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

theorem orthogonality_radial_prefactor_le {N v : ℕ} (hN : 4 ≤ N) (hv : v ≤ N) :
    64 * (4 : ℝ) ^ v ≤ (2 : ℝ) ^ (4 * (N : ℝ)) := by
  have hN' : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hv' : (v : ℝ) ≤ N := by exact_mod_cast hv
  have heq : 64 * (4 : ℝ) ^ v = (2 : ℝ) ^ (6 + 2 * (v : ℝ)) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [heq]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

theorem orthogonality_radial_bound_le_terminal {θ : ℝ} {N p v : ℕ}
    (hpar : ParameterFacts θ N) (hv : v ≤ N)
    (hw : 10 * (tolerance θ N * N) ≤ (v : ℝ) - p) :
    64 * (4 : ℝ) ^ v *
        (1024 * (expansionCount θ N : ℝ) ^ 2 /
          ((2 : ℝ) ^ v * orthogonalityLinkThreshold p (tolerance θ N * N))) ^
            expansionCount θ N ≤ (2 : ℝ) ^ (-(300 * (N : ℝ))) := by
  have hE : 0 ≤ tolerance θ N * N := by have := hpar.2.2.1.1; linarith
  have hτ : 0 < orthogonalityLinkThreshold p (tolerance θ N * N) := by
    unfold orthogonalityLinkThreshold GaugeFrostman.dyadicRadius
    positivity
  have hratio := orthogonality_radial_ratio_le hE hw hpar.2.1
  have hET : 240 * (N : ℝ) ≤ (tolerance θ N * N) * expansionCount θ N := by
    have h := mul_le_mul_of_nonneg_right
      (expansionCount_mul_tolerance_ge θ (N := N) (by have := hpar.1; omega))
      (Nat.cast_nonneg N)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  have hpow : ((2 : ℝ) ^ (-(11 * (tolerance θ N * N)))) ^ expansionCount θ N ≤
      (2 : ℝ) ^ (-(2640 * (N : ℝ))) := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  calc
    _ ≤ (2 : ℝ) ^ (4 * (N : ℝ)) * (2 : ℝ) ^ (-(2640 * (N : ℝ))) :=
      mul_le_mul (orthogonality_radial_prefactor_le hpar.1 hv)
        ((pow_le_pow_left₀ (by positivity) hratio _).trans hpow) (by positivity)
        (by positivity)
    _ = (2 : ℝ) ^ (-(2636 * (N : ℝ))) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by have := Nat.cast_nonneg (α := ℝ) N; linarith)

theorem norm_integral_orthogonalityRadialAmplitude_le_terminal {θ : ℝ} {N p v K : ℕ}
    (hpar : ParameterFacts θ N) (hv : v ≤ N)
    (hw : 10 * (tolerance θ N * N) ≤ (v : ℝ) - p)
    (hK : 6 * expansionCount θ N ≤ K) {Φ : ℝ}
    (hΦ : orthogonalityLinkThreshold p (tolerance θ N * N) / 2 ≤ |Φ|) :
    ‖∫ r : ℝ, Complex.exp (-((r * Φ : ℝ) : ℂ) * Complex.I) *
        orthogonalityRadialAmplitude K v r‖ ≤ (2 : ℝ) ^ (-(300 * (N : ℝ))) := by
  have hε := tolerance_pos θ (N := N) (by have := hpar.1; omega)
  have hT : 1 ≤ expansionCount θ N :=
    Nat.ceil_pos.mpr (by positivity)
  have hτ : 0 < orthogonalityLinkThreshold p (tolerance θ N * N) := by
    unfold orthogonalityLinkThreshold GaugeFrostman.dyadicRadius
    positivity
  exact (norm_integral_orthogonalityRadialAmplitude_le hT hK hτ hΦ).trans
    (orthogonality_radial_bound_le_terminal hpar hv hw)

end FalconerThetaGauge
