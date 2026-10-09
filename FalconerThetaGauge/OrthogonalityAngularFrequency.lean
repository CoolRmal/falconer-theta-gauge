module

public import FalconerThetaGauge.OrthogonalityAngularDecay

/-! # Literal cell geometry supplies the phase-ratio and frequency lower bounds -/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

open GaugeFrostman

theorem orthogonalityAngularPhaseRatio_le_frequency {a p v : ℕ} {E : ℝ}
    (hE : 0 ≤ E) (hgap : (p : ℝ) - a ≤ (v : ℝ) - p + 2 * E)
    {X : Fin 2 → ℤ} {x x' : Plane} (hx : x ∈ dyadicCube a X) (hx' : x' ∈ dyadicCube a X) :
    3 * ‖x - x'‖ / orthogonalityLinkThreshold p E ≤
      5 * (2 : ℝ) ^ ((v : ℝ) - p + E) := by
  have hn := norm_sub_le_of_mem_same_dyadicCube hx hx'
  have ht : 0 < orthogonalityLinkThreshold p E :=
    mul_pos (dyadicRadius_pos p) (Real.rpow_pos_of_pos (by norm_num) _)
  have he : dyadicRadius a / orthogonalityLinkThreshold p E =
      (2 : ℝ) ^ ((p : ℝ) - a - 3 * E / 2) := by
    rw [orthogonalityLinkThreshold, dyadicRadius, dyadicRadius,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  calc
    _ ≤ (9 / 2 : ℝ) * (dyadicRadius a / orthogonalityLinkThreshold p E) := by
      apply (div_le_iff₀ ht).mpr
      have heq : (9 / 2 : ℝ) * (dyadicRadius a / orthogonalityLinkThreshold p E) *
          orthogonalityLinkThreshold p E = 9 / 2 * dyadicRadius a := by field_simp
      rw [heq]
      linarith
    _ = (9 / 2 : ℝ) * (2 : ℝ) ^ ((p : ℝ) - a - 3 * E / 2) := by rw [he]
    _ ≤ 5 * (2 : ℝ) ^ ((v : ℝ) - p + E) := by
      apply mul_le_mul (by norm_num : (9 / 2 : ℝ) ≤ 5) _ (by positivity) (by norm_num)
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

theorem orthogonalityAngularPhaseLambda_le_frequency {p v : ℕ} {E r : ℝ}
    (hr : (2 : ℝ) ^ ((v : ℝ) - 2) ≤ r) :
    (2 : ℝ) ^ ((v : ℝ) - p - 4 + 3 * E / 2) ≤ r * orthogonalityLinkThreshold p E / 3 := by
  have ht : 0 < orthogonalityLinkThreshold p E :=
    mul_pos (dyadicRadius_pos p) (Real.rpow_pos_of_pos (by norm_num) _)
  have he : (2 : ℝ) ^ ((v : ℝ) - 2) * orthogonalityLinkThreshold p E =
      4 * (2 : ℝ) ^ ((v : ℝ) - p - 4 + 3 * E / 2) := by
    calc
      _ = (2 : ℝ) ^ ((v : ℝ) - 2 - p + 3 * E / 2) := by
        rw [orthogonalityLinkThreshold, dyadicRadius,
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring
      _ = (2 : ℝ) ^ (2 : ℝ) * (2 : ℝ) ^ ((v : ℝ) - p - 4 + 3 * E / 2) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring
      _ = _ := by norm_num
  have hh := mul_le_mul_of_nonneg_right hr ht.le
  rw [he] at hh
  have hp : 0 ≤ (2 : ℝ) ^ ((v : ℝ) - p - 4 + 3 * E / 2) := by positivity
  linarith

end FalconerThetaGauge
