/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntryOrthogonality

/-! # Source 9.3 Step 3 for each actual retained original probability -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- The genuine entry cost is at most `gain + blockParameter + 12*tolerance`. -/
theorem regularRetainedRootSelfEnergy_le_entry_state (μ : Measure Plane)
    [IsProbabilityMeasure μ] {θ C : ℝ} (hθ : 0 < θ) (hC : 0 < C)
    (hball : HasGaugeBallBound μ θ C) {N : ℕ} (hpar : ParameterFacts θ N)
    (hconstant : Real.log C / Real.log 2 ≤ blockParameter θ N * N / 2)
    (t : RegularRetainedType μ θ N) :
    let ρ := regularRetainedProbability μ θ N t
    let c := regularMeasureEntryDepth ρ θ N
    regularRetainedRootSelfEnergy μ θ N (8 * expansionCount θ N) t ≤
      (2 : ℝ) ^ (N * (gain θ N + blockParameter θ N + 12 * tolerance θ N)) *
        regularMeasureStateEnergy ρ θ N 0 (.fourier c N c N) +
          (2 : ℝ) ^ (-(80 * (N : ℝ))) := by
  let ρ := regularRetainedProbability μ θ N t
  let c := regularMeasureEntryDepth ρ θ N
  have hp := regularDyadicPartMeasure_probability μ (tolerance θ N) (blockParameter θ N)
    N t.property
  let : IsProbabilityMeasure ρ := hp.1
  have he := regularDyadicPart_entry_properties μ hθ hC hball hpar hconstant t.property
  have hreg := regularDyadicPartMeasure_isRegularThrough μ hpar.2.2.1.1 t.val
  have h := rootPieceFourierEnergy_le_entry_state ρ hp.2 hpar hreg he.2.1
  have hheight : profileHeight (regularMeasureExcess ρ N) c 0 c ≤
      gain θ N + blockParameter θ N := he.2.2.2.2.2
  apply h.trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_right _ (regularMeasureStateEnergy_nonneg ρ θ N 0 _)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  exact mul_le_mul_of_nonneg_left (add_le_add hheight le_rfl) (Nat.cast_nonneg N)

end FalconerThetaGauge
