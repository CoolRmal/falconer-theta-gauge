module

public import FalconerThetaGauge.SpaceSplittingEqualSignBudget

/-! # The two literal equal-sign radial series have negligible source size -/

@[expose] public section

noncomputable section

open MeasureTheory Finset

namespace FalconerThetaGauge

def spaceSplittingBuiltEqualSignSeries (K v T : ℕ) (b₁ b₂ : Plane → UnitCircle → ℝ)
    (x x' y y' : Plane) : ℂ :=
  spaceSplittingEqualSignRadialSeries K v T (dist x x') (dist y y')
    (builtSymbolPairAngularAmplitude b₁ b₁ x x')
    (builtSymbolPairAngularAmplitude b₂ b₂ y y')
    (radialAngle 0 (x - x')) (radialAngle 0 (y - y'))

theorem norm_spaceSplittingBuiltEqualSignSeries_le_source
    {ρ : Measure Plane} {θ : ℝ} {N L v : ℕ} (hpar : ParameterFacts θ N)
    (I : Finset ProfileScheduleTest) (hcard : I.card ≤ N ^ 2 + 1) (hv : v ≤ N)
    {h width : ℝ} (hh : h ≤ N)
    (hgap : 2 * max (L : ℝ) (tolerance θ N * N) ≤ (v : ℝ) - h)
    (hlength : ∀ test ∈ I, test.length ≤ L) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ (tolerance θ N * N) width
      (8 * expansionCount θ N) I (2 * expansionCount θ N))
    (hb₂ : b₂ ∈ scheduledSymbolClass ρ (tolerance θ N * N) width
      (8 * expansionCount θ N) I (2 * expansionCount θ N))
    {x x' y y' : Plane}
    (hdx : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ dist x x')
    (hdy : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ dist y y') :
    ‖spaceSplittingBuiltEqualSignSeries (8 * expansionCount θ N) v
      (expansionCount θ N) b₁ b₂ x x' y y'‖ ≤ (2 : ℝ) ^ (-390 * (N : ℝ)) := by
  let T := expansionCount θ N
  let dx := dist x x'
  let dy := dist y y'
  let Gx := builtSymbolPairAngularAmplitude b₁ b₁ x x'
  let Gy := builtSymbolPairAngularAmplitude b₂ b₂ y y'
  let φx := radialAngle 0 (x - x')
  let φy := radialAngle 0 (y - y')
  let C : ℂ := (2 * Real.pi / Real.sqrt (dx * dy) : ℝ)
  let f (j k : ℕ) : ℂ := C *
    (Complex.I * (stationaryPhaseOperator j Gx φx / (dx : ℂ) ^ j) *
      (stationaryPhaseOperator k Gy φy / (dy : ℂ) ^ k) *
        spaceSplittingRadialMoment (8 * T) v (1 - (j : ℤ) - k) (dx + dy) -
     Complex.I * (stationaryPhaseConjugateOperator j Gx (φx + Real.pi) / (dx : ℂ) ^ j) *
      (stationaryPhaseConjugateOperator k Gy (φy + Real.pi) / (dy : ℂ) ^ k) *
        spaceSplittingRadialMoment (8 * T) v (1 - (j : ℤ) - k) (-(dx + dy)))
  have hx : 0 < dx := lt_of_lt_of_le (by positivity) hdx
  have hy : 0 < dy := lt_of_lt_of_le (by positivity) hdy
  have hterm (j : ℕ) (hj : j ∈ range T) (k : ℕ) (hk : k ∈ range T) :
      ‖f j k‖ ≤ 2 * (2 : ℝ) ^ (-400 * (N : ℝ)) := by
    have hj' := mem_range.1 hj
    have hk' := mem_range.1 hk
    have h₁ := norm_spaceSplitting_equal_coefficient_moment_le_source hpar I hcard hv hh
      hgap hdx hdy (by rw [abs_of_pos (add_pos hx hy)]; linarith : dx ≤ |dx + dy|) hj' hk'
      (norm_stationaryPhaseOperator_builtPair_le hlength hb₁ hj' x x' φx)
      (norm_stationaryPhaseOperator_builtPair_le hlength hb₂ hk' y y' φy)
    have h₂ := norm_spaceSplitting_equal_coefficient_moment_le_source hpar I hcard hv hh
      hgap hdx hdy (by rw [abs_neg, abs_of_pos (add_pos hx hy)]; linarith :
        dx ≤ |-(dx + dy)|) hj' hk'
      (norm_stationaryPhaseConjugateOperator_builtPair_le hlength hb₁ hj' x x'
        (φx + Real.pi))
      (norm_stationaryPhaseConjugateOperator_builtPair_le hlength hb₂ hk' y y'
        (φy + Real.pi))
    change ‖C * ((stationaryPhaseOperator j Gx φx / (dx : ℂ) ^ j) *
      (stationaryPhaseOperator k Gy φy / (dy : ℂ) ^ k) *
        spaceSplittingRadialMoment (8 * T) v (1 - (j : ℤ) - k) (dx + dy))‖ ≤ _ at h₁
    change ‖C * ((stationaryPhaseConjugateOperator j Gx (φx + Real.pi) / (dx : ℂ) ^ j) *
      (stationaryPhaseConjugateOperator k Gy (φy + Real.pi) / (dy : ℂ) ^ k) *
        spaceSplittingRadialMoment (8 * T) v (1 - (j : ℤ) - k) (-(dx + dy)))‖ ≤ _ at h₂
    dsimp only [f]
    have he : C * (Complex.I * (stationaryPhaseOperator j Gx φx / (dx : ℂ) ^ j) *
        (stationaryPhaseOperator k Gy φy / (dy : ℂ) ^ k) *
          spaceSplittingRadialMoment (8 * T) v (1 - (j : ℤ) - k) (dx + dy) -
      Complex.I * (stationaryPhaseConjugateOperator j Gx (φx + Real.pi) / (dx : ℂ) ^ j) *
        (stationaryPhaseConjugateOperator k Gy (φy + Real.pi) / (dy : ℂ) ^ k) *
          spaceSplittingRadialMoment (8 * T) v (1 - (j : ℤ) - k) (-(dx + dy))) =
      Complex.I * (C * ((stationaryPhaseOperator j Gx φx / (dx : ℂ) ^ j) *
        (stationaryPhaseOperator k Gy φy / (dy : ℂ) ^ k) *
          spaceSplittingRadialMoment (8 * T) v (1 - (j : ℤ) - k) (dx + dy))) -
      Complex.I * (C * ((stationaryPhaseConjugateOperator j Gx (φx + Real.pi) /
          (dx : ℂ) ^ j) *
        (stationaryPhaseConjugateOperator k Gy (φy + Real.pi) / (dy : ℂ) ^ k) *
          spaceSplittingRadialMoment (8 * T) v (1 - (j : ℤ) - k) (-(dx + dy)))) := by ring
    rw [he]
    exact (norm_sub_le _ _).trans (by
      simp only [norm_mul, Complex.norm_I, one_mul] at h₁ h₂ ⊢
      linarith)
  have he : spaceSplittingBuiltEqualSignSeries (8 * T) v T b₁ b₂ x x' y y' =
      ∑ j ∈ range T, ∑ k ∈ range T, f j k := by
    unfold spaceSplittingBuiltEqualSignSeries spaceSplittingEqualSignRadialSeries
    simp only [mul_sum]
    rfl
  rw [he]
  calc
    _ ≤ ∑ j ∈ range T, ∑ k ∈ range T, ‖f j k‖ :=
      (norm_sum_le _ _).trans (sum_le_sum (fun _ _ ↦ norm_sum_le _ _))
    _ ≤ ∑ j ∈ range T, ∑ k ∈ range T, 2 * (2 : ℝ) ^ (-400 * (N : ℝ)) :=
      sum_le_sum (fun j hj ↦ sum_le_sum (fun k hk ↦ hterm j hj k hk))
    _ = (2 * (T : ℝ) ^ 2) * (2 : ℝ) ^ (-400 * (N : ℝ)) := by simp; ring
    _ ≤ (2 : ℝ) ^ (N : ℝ) * (2 : ℝ) ^ (-400 * (N : ℝ)) :=
      mul_le_mul_of_nonneg_right (two_stationary_count_square_le_terminal hpar) (by positivity)
    _ = (2 : ℝ) ^ (-399 * (N : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by have := Nat.cast_nonneg (α := ℝ) N; linarith)

end FalconerThetaGauge
