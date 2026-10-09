module

public import FalconerThetaGauge.ScheduledStateEnergiesLeaf
public import FalconerThetaGauge.DirectionalTestsAverage

/-! # The genuine state-level low/high step at the exact rounded tolerance numerator -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- The actual normalized Fourier shell of a literal level-masked distance measure. -/
def profileMaskedDistanceHighShellEnergy (ρ : Measure Plane) (A : ℕ → ℝ)
    (q N : ℕ) (E : ℝ) (levels i K a t v : ℕ) : ℝ :=
  finiteEnergyMaximum (profileSeparatedCellPairs ρ a) fun P ↦
    scalarDyadicFourierShellIntegral
      (levelMaskedDistanceMeasure ρ ρ (dyadicCube a P.1) (dyadicCube a P.2) E levels i K
        (profileScheduledTests A q N a t) (profileScheduledTests A q N a t)) v /
      (ρ.real (dyadicCube a P.1) * ρ.real (dyadicCube a P.2))

theorem profileMaskedDistanceHighShellEnergy_nonneg (ρ : Measure Plane) (A : ℕ → ℝ)
    (q N : ℕ) (E : ℝ) (levels i K a t v : ℕ) :
    0 ≤ profileMaskedDistanceHighShellEnergy ρ A q N E levels i K a t v :=
  finiteEnergyMaximum_nonneg _ _

theorem normalizedShell_le_profileMaskedDistanceHighShellEnergy (ρ : Measure Plane)
    (A : ℕ → ℝ) (q N : ℕ) (E : ℝ) (levels i K a t v : ℕ) {P Q : Fin 2 → ℤ}
    (hP : P ∈ occupiedUnitCells ρ a) (hQ : Q ∈ occupiedUnitCells ρ a)
    (hsep : SeparatedDyadicCells a P Q) :
    scalarDyadicFourierShellIntegral
        (levelMaskedDistanceMeasure ρ ρ (dyadicCube a P) (dyadicCube a Q) E levels i K
          (profileScheduledTests A q N a t) (profileScheduledTests A q N a t)) v /
        (ρ.real (dyadicCube a P) * ρ.real (dyadicCube a Q)) ≤
      profileMaskedDistanceHighShellEnergy ρ A q N E levels i K a t v := by
  unfold profileMaskedDistanceHighShellEnergy
  apply le_finiteEnergyMaximum (profileSeparatedCellPairs ρ a)
    (fun R ↦ scalarDyadicFourierShellIntegral
      (levelMaskedDistanceMeasure ρ ρ (dyadicCube a R.1) (dyadicCube a R.2) E levels i K
        (profileScheduledTests A q N a t) (profileScheduledTests A q N a t)) v /
      (ρ.real (dyadicCube a R.1) * ρ.real (dyadicCube a R.2))) (j := (P, Q))
  exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hP, hQ⟩, hsep⟩

theorem profileDistanceStateEnergy_low_high (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) (A : ℕ → ℝ) {q N : ℕ} (hq : 0 < q) {δ : ℕ}
    {levels : ℕ} (hlevels : 0 < levels) (hsize : (levels : ℝ) ≤ (2 : ℝ) ^ (δ : ℝ) / 8)
    (i K a t : ℕ) (ht : t ≤ N) (hfreq : a < t - δ) :
    profileDistanceStateEnergy ρ A q N (δ : ℝ) levels i a t ≤
      320 * profileDistanceStateEnergy ρ A q N (δ : ℝ) levels (i + 1) a (t - δ) +
      320 * ∑ v ∈ scalarHighDyadicIndices ((t - δ : ℕ) : ℝ) t,
        profileMaskedDistanceHighShellEnergy ρ A q N (δ : ℝ) levels i K a t v := by
  have hδt : δ ≤ t := by omega
  have hcast : ((t - δ : ℕ) : ℝ) = (t : ℝ) - δ := Nat.cast_sub hδt
  have hbound : 0 ≤ 320 * profileDistanceStateEnergy ρ A q N (δ : ℝ) levels (i + 1) a
      (t - δ) + 320 * ∑ v ∈ scalarHighDyadicIndices ((t - δ : ℕ) : ℝ) t,
        profileMaskedDistanceHighShellEnergy ρ A q N (δ : ℝ) levels i K a t v := by
    exact add_nonneg (mul_nonneg (by norm_num) (profileDistanceStateEnergy_nonneg ..))
      (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ ↦
        profileMaskedDistanceHighShellEnergy_nonneg ..))
  apply finiteEnergyMaximum_le _ _ hbound
  intro pair hpair
  obtain ⟨hpair, hsep⟩ := Finset.mem_filter.1 hpair
  obtain ⟨hP, hQ⟩ := Finset.mem_product.1 hpair
  have hbridge := scheduledDistanceEnergy_cells_low_high ρ ρ hρ hρ hsep
    (Nat.cast_nonneg δ) hlevels hsize i K (profileScheduledTests A q N a t)
    (profileScheduledTests A q N a t) (profileScheduledTests_ordered A hq ht)
    (profileScheduledTests_ordered A hq ht) t
    (by rw [← hcast]; exact_mod_cast hfreq)
  rw [← hcast, realMaskedDistanceEnergy_nat] at hbridge
  have hlow : scheduledDistanceEnergy ρ ρ (dyadicCube a pair.1) (dyadicCube a pair.2)
      (δ : ℝ) (directionalLevelWidth levels (i + 1)) (profileScheduledTests A q N a t)
      (profileScheduledTests A q N a t) (t - δ) ≤
        profileDistanceStateEnergy ρ A q N (δ : ℝ) levels (i + 1) a (t - δ) := by
    apply (scheduledDistanceEnergy_mono ρ ρ (measurableSet_dyadicCube a pair.1)
      (measurableSet_dyadicCube a pair.2) (dyadicRadius_pos a)
      (fun _x hx _y hy ↦ by
        have hd := (dist_bounds_of_separatedDyadicCells hsep hx hy).1
        linarith [dyadicRadius_pos a]) (δ : ℝ) (le_refl _)
      (profileScheduledTests_mono A q N (le_refl a) (Nat.sub_le t δ))
      (profileScheduledTests_mono A q N (le_refl a) (Nat.sub_le t δ)) (t - δ)).trans
    exact scheduledDistanceEnergy_le_profileDistanceStateEnergy ρ A q N _ _ _ _ _ hP hQ hsep
  apply hbridge.trans
  apply add_le_add (mul_le_mul_of_nonneg_left hlow (by norm_num))
  simp only [div_eq_mul_inv, mul_assoc, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  have hs := normalizedShell_le_profileMaskedDistanceHighShellEnergy ρ A q N
    (δ : ℝ) levels i K a t v hP hQ hsep
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 320)

end FalconerThetaGauge
