module

public import FalconerThetaGauge.MaskedDistanceEnergyBridge
public import FalconerThetaGauge.RegularMeasureEntryPieceLists

/-! # The actual recursive piece lists satisfy the depth orders used by the analytic bridge -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function

namespace FalconerThetaGauge

theorem profileScheduledTests_ordered (A : ℕ → ℝ) {q N a t : ℕ}
    (hq : 0 < q) (ht : t ≤ N) : ScheduledTestsOrdered (profileScheduledTests A q N a t) := by
  constructor
  · intro test htest hkind
    obtain ⟨_, _, _, _, _, _, hlength, _⟩ := profileScheduledTests_origin hq ht htest
    simp only [ProfileScheduleTest.length, hkind] at hlength
    omega
  · intro test htest hkind
    obtain ⟨_, _, _, _, _, _, hlength, _⟩ := profileScheduledTests_origin hq ht htest
    simp only [ProfileScheduleTest.length, hkind] at hlength
    omega

theorem profilePieceTests_ordered (A : ℕ → ℝ) {q N c : ℕ} (hq : 0 < q) :
    ScheduledTestsOrdered (profilePieceTests A q N c) := by
  have hs := profileScheduledTests_ordered A hq (le_refl N) (a := c)
  constructor
  · intro test htest hkind
    rcases Finset.mem_union.1 htest with hentry | hscheduled
    · have heq : test = ⟨.tube, c, 0⟩ := Finset.mem_singleton.1 hentry
      subst test
      exact Nat.zero_le c
    · exact hs.1 test hscheduled hkind
  · intro test htest hkind
    rcases Finset.mem_union.1 htest with hentry | hscheduled
    · have heq : test = ⟨.tube, c, 0⟩ := Finset.mem_singleton.1 hentry
      subst test
      cases hkind
    · exact hs.2 test hscheduled hkind

theorem regularMeasurePieceTests_ordered (ρ : Measure Plane) {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) : ScheduledTestsOrdered (regularMeasurePieceTests ρ θ N) :=
  profilePieceTests_ordered _ (blockCount_pos θ (by have := hpar.1; omega))

end FalconerThetaGauge
