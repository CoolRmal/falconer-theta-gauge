module

public import FalconerThetaGauge.DistanceLinearizationDirections
public import FalconerThetaGauge.DirectionalTestsAverage

/-! # Actual retained fine-cell pairs pass the narrower tests of source §7.7 -/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem linearization_direction_motion_le_test_scale {a p ℓ : ℕ} {E : ℝ}
    (hE : 0 ≤ E) (hℓ : a + ℓ ≤ p) :
    (2 / 125 : ℝ) * (2 : ℝ) ^ ((a : ℝ) - p) ≤
      2 * ((2 : ℝ) ^ (-(ℓ : ℝ)) * (2 : ℝ) ^ E) := by
  have hcast : (a : ℝ) + ℓ ≤ p := by exact_mod_cast hℓ
  have hpow : (2 : ℝ) ^ ((a : ℝ) - p) ≤ (2 : ℝ) ^ (-(ℓ : ℝ) + E) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  calc
    _ ≤ (2 / 125 : ℝ) * (2 : ℝ) ^ (-(ℓ : ℝ) + E) :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ ≤ 2 * (2 : ℝ) ^ (-(ℓ : ℝ) + E) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = _ := by rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]

/-- The actual witness in one fine-cell pair certifies every shorter retained
test for every pair in those same cells, at the next narrower width. -/
theorem retained_pair_scheduled_passing (ρ : Measure Plane) [IsFiniteMeasure ρ]
    {a p : ℕ} {A B P Q R : Fin 2 → ℤ} (hsep : SeparatedDyadicCells a A B)
    (hP : dyadicCube p P ⊆ dyadicCube a A) (hQ : dyadicCube p Q ⊆ dyadicCube a B)
    {E width width' : ℝ} (hE : 0 ≤ E)
    (hgap : 8 * (2 : ℝ) ^ (-E) ≤ width - width') (test : ProfileScheduleTest)
    (htube : test.kind = .tube → test.endpoint ≤ test.anchor)
    (hprojection : test.kind = .projection → test.anchor ≤ test.endpoint)
    (hℓ : a + test.length ≤ p) (hR : 0 < unitCellWeight ρ test.anchor R)
    {x y x₀ y₀ : Plane} (hx : x ∈ dyadicCube p P) (hy : y ∈ dyadicCube p Q)
    (hx₀ : x₀ ∈ dyadicCube p P) (hy₀ : y₀ ∈ dyadicCube p Q)
    (hw₀ : pairDirection x₀ y₀ ∈ scheduledPassingDirections ρ E width test R) :
    pairDirection x y ∈ scheduledPassingDirections ρ E width' test R := by
  apply (scheduledDirectionalCount_le_of_norm_sub_scale ρ E hgap test htube hprojection R hR
    ((norm_pairDirection_sub_cells_le hsep hP hQ hx hy hx₀ hy₀).trans
      (linearization_direction_motion_le_test_scale hE hℓ))).trans hw₀

/-- The projection test `[p,t]` at the actual center direction follows from
one genuine passing witness and the strict linearization depth condition. -/
theorem retained_center_projection_passing (ρ : Measure Plane) [IsFiniteMeasure ρ]
    {a p t : ℕ} {A B P Q : Fin 2 → ℤ} (hsep : SeparatedDyadicCells a A B)
    (hP : dyadicCube p P ⊆ dyadicCube a A) (hQ : dyadicCube p Q ⊆ dyadicCube a B)
    (hpt : p ≤ t) (hdepth : a + t < 2 * p) {E width width' : ℝ} (hE : 0 ≤ E)
    (hgap : 8 * (2 : ℝ) ^ (-E) ≤ width - width')
    (hQocc : 0 < unitCellWeight ρ p Q) {x₀ y₀ : Plane}
    (hx₀ : x₀ ∈ dyadicCube p P) (hy₀ : y₀ ∈ dyadicCube p Q)
    (hw₀ : pairDirection x₀ y₀ ∈ projectionPassingDirections ρ p t E width Q) :
    pairDirection (dyadicCellCenter p P) (dyadicCellCenter p Q) ∈
      projectionPassingDirections ρ p t E width' Q := by
  have h := retained_pair_scheduled_passing ρ hsep hP hQ hE hgap
    (⟨.projection, p, t⟩ : ProfileScheduleTest) (by simp) (by simpa using hpt)
    (by change a + (t - p) ≤ p; omega) hQocc
    (dyadicCellCenter_mem_dyadicCube p P) (dyadicCellCenter_mem_dyadicCube p Q) hx₀ hy₀
  exact h hw₀

/-- The source's literal one-cell coefficient `B` is bounded at the actual
center direction by the regular profile height and the actual `(P1)` budget. -/
theorem retained_center_projection_count_le_height (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {θ : ℝ} {N a p t : ℕ} (hpar : ParameterFacts θ N)
    (hreg : IsRegularThrough (tolerance θ N) N ρ) {A B P Q : Fin 2 → ℤ}
    (hsep : SeparatedDyadicCells a A B) (hP : dyadicCube p P ⊆ dyadicCube a A)
    (hQ : dyadicCube p Q ⊆ dyadicCube a B) (hpt : p ≤ t) (ht : t ≤ N)
    (hdepth : a + t < 2 * p) {width width' : ℝ} (hwidth' : 1 ≤ width')
    (hgap : 8 * (2 : ℝ) ^ (-(tolerance θ N * N)) ≤ width - width')
    (hQocc : 0 < unitCellWeight ρ p Q) {x₀ y₀ : Plane}
    (hx₀ : x₀ ∈ dyadicCube p P) (hy₀ : y₀ ∈ dyadicCube p Q)
    (hw₀ : pairDirection x₀ y₀ ∈
      projectionPassingDirections ρ p t (tolerance θ N * N) width Q) :
    projectionCount ρ p t (tolerance θ N * N) 1 Q
        (pairDirection (dyadicCellCenter p P) (dyadicCellCenter p Q)) ≤
      (2 : ℝ) ^ (-((t : ℝ) - p)) * (2 : ℝ) ^ ((N : ℝ) *
        (profileHeight (regularMeasureExcess ρ N) p p t + 6 * tolerance θ N)) := by
  have hN : 0 < N := by have := hpar.1; omega
  have hε := (tolerance_pos θ hN).le
  have hpassing := retained_center_projection_passing ρ hsep hP hQ hpt hdepth
    (mul_nonneg hε (Nat.cast_nonneg N)) hgap hQocc hx₀ hy₀ hw₀
  have hcount := projectionCount_le_height_of_passing ρ hρ hε hN hreg hpt ht Q hQocc
    hpar.directional_average_budgets.2 hpassing
  have hw := scheduledDirectionalCount_mono_width ρ (tolerance θ N * N) hwidth'
    (⟨.projection, p, t⟩ : ProfileScheduleTest) Q hQocc
    (pairDirection (dyadicCellCenter p P) (dyadicCellCenter p Q))
  exact hw.trans hcount

end FalconerThetaGauge
