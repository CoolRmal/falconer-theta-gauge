/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.DirectionalTestsPiecesSmooth

/-! # Quantitative derivative regularity for the actual finite test products -/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset
open scoped Classical ContDiff

namespace FalconerThetaGauge

def scheduledTestDerivativeScale (T : ℕ) (E : ℝ) (test : ProfileScheduleTest) : ℝ :=
  (4 * (T : ℝ)) ^ 3 / scheduledMaskScale E test

theorem one_le_scheduledTestDerivativeScale {T : ℕ} (hT : 2 ≤ T) (E : ℝ)
    (test : ProfileScheduleTest) : 1 ≤ scheduledTestDerivativeScale T E test := by
  have hT' : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hnum : 1 ≤ (4 * (T : ℝ)) ^ 3 := one_le_pow₀ (by linarith)
  have hscale : scheduledMaskScale E test ≤ 1 := min_le_left _ _
  exact (le_div_iff₀ (scheduledMaskScale_pos E test)).mpr (by linarith)

theorem iteratedDeriv_ofReal_eq {f : ℝ → ℝ} {n : ℕ} {x : ℝ}
    (hf : ContDiffAt ℝ n f x) :
    iteratedDeriv n (fun y => (f y : ℂ)) x = ((iteratedDeriv n f x : ℝ) : ℂ) := by
  simpa only [Complex.real_smul, mul_one] using iteratedDeriv_smul_const hf (1 : ℂ)

/-- One literal convolution mask has its proved derivative bounds through order `6T`. -/
theorem scheduledTestSymbol_isDerivativeRegular (ρ : Measure Plane) (E : ℝ)
    (test : ProfileScheduleTest) {T : ℕ} (hT : 2 ≤ T) (x : Plane) :
    IsDerivativeRegular 1 (scheduledTestDerivativeScale T E test) (6 * T)
      (fun α => (scheduledTestSymbol ρ E test (6 * T) x (unitCircleOfAngle α) : ℂ)) := by
  have hf := contDiff_scheduledTestSymbol_comp_angle ρ E test (6 * T) x
  refine ⟨by norm_num, one_le_scheduledTestDerivativeScale hT E test,
    (Complex.ofRealCLM.contDiff.comp hf).of_le
      (ENat.natCast_le_of_coe_top_le_withTop (le_refl ∞) (6 * T)), ?_⟩
  intro k hk α
  rw [iteratedDeriv_ofReal_eq ((hf.of_le (by simp)).contDiffAt)]
  simpa only [Complex.norm_real, Real.norm_eq_abs, one_mul, scheduledTestDerivativeScale] using
    norm_iteratedDeriv_scheduledTestSymbol_comp_angle_le ρ E test hT hk x α

/-- Leibniz gives the exact sum of the literal mask derivative scales. -/
theorem scheduledTestProduct_isDerivativeRegular (ρ : Measure Plane) (E : ℝ)
    (I : Finset ProfileScheduleTest) (hI : I.Nonempty) {T : ℕ} (hT : 2 ≤ T) (x : Plane) :
    IsDerivativeRegular 1 (∑ test ∈ I, scheduledTestDerivativeScale T E test) (6 * T)
      (fun α => ((∏ test ∈ I,
        scheduledTestSymbol ρ E test (6 * T) x (unitCircleOfAngle α) : ℝ) : ℂ)) := by
  have hp := IsDerivativeRegular.prod I hI (fun _ => 1)
    (scheduledTestDerivativeScale T E)
    (fun test α => (scheduledTestSymbol ρ E test (6 * T) x (unitCircleOfAngle α) : ℂ)) (6 * T)
    (fun test _ => scheduledTestSymbol_isDerivativeRegular ρ E test hT x)
  have heq : (∏ test ∈ I, fun α =>
      (scheduledTestSymbol ρ E test (6 * T) x (unitCircleOfAngle α) : ℂ)) =
      (fun α => ((∏ test ∈ I,
        scheduledTestSymbol ρ E test (6 * T) x (unitCircleOfAngle α) : ℝ) : ℂ)) := by
    ext α
    simp only [Finset.prod_apply, Complex.ofReal_prod]
  simpa only [Finset.prod_const_one, heq] using hp

/-- At each pin in a retained piece, the global symbol has the derivative bound of
exactly that piece's actual test product. -/
theorem regularDirectionalFilter_symbol_isDerivativeRegular_on_piece (μ : Measure Plane)
    [IsProbabilityMeasure μ] {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N)
    {T : ℕ} (hT : 2 ≤ T)
    (t : {t // t ∈ regularDyadicKeptTypes μ (tolerance θ N) (blockParameter θ N) N})
    {x : Plane} (hx : x ∈ regularDyadicPartCarrier μ (tolerance θ N) N t.val) :
    let ρ := regularDyadicPartMeasure μ (tolerance θ N) N t.val
    IsDerivativeRegular 1
      (∑ test ∈ regularMeasurePieceTests ρ θ N,
        scheduledTestDerivativeScale T (tolerance θ N * N) test) (6 * T)
      (fun α =>
        ((regularDirectionalFilter μ hpar (6 * T)).symbol x (unitCircleOfAngle α) : ℂ)) := by
  simp_rw [regularDirectionalFilter_symbol_eq_piece_product μ hpar (6 * T) t hx]
  apply scheduledTestProduct_isDerivativeRegular _ _ _ _ hT x
  exact ⟨⟨.tube, regularMeasureEntryDepth
    (regularDyadicPartMeasure μ (tolerance θ N) N t.val) θ N, 0⟩,
    Finset.mem_union_left _ (Finset.mem_singleton.mpr rfl)⟩

end FalconerThetaGauge
