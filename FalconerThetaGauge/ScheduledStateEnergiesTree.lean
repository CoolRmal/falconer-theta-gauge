module

public import FalconerThetaGauge.ScheduledStateEnergiesMoveTwo
public import FalconerThetaGauge.RegularMeasureEntryTreeVisits
public import FalconerThetaGauge.RegularMeasureEntryTreeLevels

/-! # Genuine terminal energy summed with every path multiplicity in the actual induction tree -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeSeparatedMeasures

theorem profileInductionLevelVisits_initial {A : ℕ → ℝ} {q N δ : ℕ}
    {s : ProfileChainState} (hs : s.Valid N δ) {m : ℕ} {chain : ProfileMoveChain A q N δ}
    (hchain : chain ∈ profileInductionLevelVisits A q N δ s hs m) : chain.state 0 = s := by
  induction m generalizing chain with
  | zero =>
    have heq := Multiset.mem_singleton.1 hchain
    subst chain
    rfl
  | succ m ih =>
    obtain ⟨parent, hparent, hchild⟩ := Multiset.mem_bind.1 hchain
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 hchild
    simpa only [ProfileMoveChain.append, Nat.zero_le, ite_true] using ih hparent

theorem profileInductionVisits_initial {A : ℕ → ℝ} {θ : ℝ} {N : ℕ}
    {s : ProfileChainState} (hs : s.Valid N (toleranceCount θ N))
    {chain : ProfileMoveChain A (blockCount θ N) N (toleranceCount θ N)}
    (hchain : chain ∈ profileInductionVisits A θ N s hs) : chain.state 0 = s := by
  obtain ⟨m, _, hm⟩ := Multiset.mem_sum.1 hchain
  exact profileInductionLevelVisits_initial hs hm

/-- Actual short leaf visits, retaining every multiplicity of the complete concrete recurrence. -/
def profileTerminalLeafVisits (A : ℕ → ℝ) (θ : ℝ) (N : ℕ) (s : ProfileChainState)
    (hs : s.Valid N (toleranceCount θ N)) :
    Multiset (ProfileMoveChain A (blockCount θ N) N (toleranceCount θ N)) :=
  (profileInductionVisits A θ N s hs).filter fun chain ↦
    (chain.state chain.length).finish - (chain.state chain.length).start ≤ 100 * blockCount θ N

def actualProfileTreeTerminalEnergy (ρ : Measure Plane) (θ : ℝ) (N : ℕ)
    (s : ProfileChainState) (hs : s.Valid N (toleranceCount θ N)) (initialLevel : ℕ) : ℝ :=
  ((profileTerminalLeafVisits (regularMeasureExcess ρ N) θ N s hs).map fun chain ↦
    chain.multiplierProduct (tolerance θ N) *
      regularMeasureStateEnergy ρ θ N (chain.maskLevel initialLevel) (chain.state chain.length)).sum

/-- The actual multiplicity-preserving terminal contribution needs only `226κ`
of the source budget. -/
theorem actualProfileTreeTerminalEnergy_le_budget (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N)
    (s : ProfileChainState) (hs : s.Valid N (toleranceCount θ N))
    (hroot : 10 * blockCount θ N ≤ s.finish - s.start) (initialLevel : ℕ) :
    actualProfileTreeTerminalEnergy ρ θ N s hs initialLevel ≤
      (2 : ℝ) ^ (N * (-profileBudget (regularMeasureExcess ρ N) (blockCount θ N)
        s.start s.finish + 226 * blockParameter θ N)) := by
  let leaves := profileTerminalLeafVisits (regularMeasureExcess ρ N) θ N s hs
  let C := (2 : ℝ) ^ (N * (-profileBudget (regularMeasureExcess ρ N) (blockCount θ N)
    s.start s.finish + 225 * blockParameter θ N))
  have hbound : ∀ z ∈ leaves.map (fun chain ↦ chain.multiplierProduct (tolerance θ N) *
      regularMeasureStateEnergy ρ θ N (chain.maskLevel initialLevel) (chain.state chain.length)),
      z ≤ C := by
    intro z hz
    obtain ⟨chain, hchain, rfl⟩ := Multiset.mem_map.1 hz
    obtain ⟨hvisit, hshort⟩ := Multiset.mem_filter.1 hchain
    have hstart := profileInductionVisits_initial hs hvisit
    have h := actual_weighted_short_leaf_le_budget ρ hρ hpar chain
      (by simpa only [hstart] using hroot) hshort (chain.maskLevel initialLevel)
    simpa only [hstart] using h
  have hsum := Multiset.sum_le_card_nsmul _ C hbound
  simp only [Multiset.card_map, nsmul_eq_mul] at hsum
  have hcard : (leaves.card : ℝ) ≤ (2 : ℝ) ^ (blockParameter θ N * N) := by
    have hle : leaves.card ≤ (profileInductionVisits (regularMeasureExcess ρ N) θ N s hs).card :=
      Multiset.card_le_card (Multiset.filter_le _ _)
    exact (Nat.cast_le.2 hle).trans (profileInductionVisits_card_le_block_power hpar hs)
  calc
    _ ≤ (leaves.card : ℝ) * C := hsum
    _ ≤ (2 : ℝ) ^ (blockParameter θ N * N) * C :=
      mul_le_mul_of_nonneg_right hcard (by dsimp [C]; positivity)
    _ = _ := by
      dsimp only [C]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

end FalconerThetaGauge
