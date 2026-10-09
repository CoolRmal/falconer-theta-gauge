module

public import FalconerThetaGauge.RadialProjectionDefinitions

/-!
# Continuity away from the radial diagonal

The angular argument has a branch cut, but the actual unit-circle projection is
continuous off the diagonal. This is the continuity used by the weak-limit step
of Theorem 5.4 on separated source and pin supports.
-/

@[expose] public section

noncomputable section

open Set

namespace FalconerThetaGauge

/-- The genuine circle-valued radial projection is jointly continuous off the diagonal. -/
theorem continuousOn_radialProjection :
    ContinuousOn (Function.uncurry radialProjection) {p : Plane × Plane | p.1 ≠ p.2} := by
  apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
  change ContinuousOn (fun p : Plane × Plane ↦ (radialProjection p.1 p.2 : Plane)) _
  have hvec : Continuous (fun p : Plane × Plane ↦ p.2 - p.1) := continuous_snd.sub continuous_fst
  have hinv : ContinuousOn (fun p : Plane × Plane ↦ ‖p.2 - p.1‖⁻¹)
      {p : Plane × Plane | p.1 ≠ p.2} := by
    apply hvec.norm.continuousOn.inv₀
    intro p hp
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hp))
  apply (hinv.smul hvec.continuousOn).congr
  intro p hp
  exact coe_radialProjection_of_ne hp

/-- Quantitative separation keeps the whole source/pin product in the continuity domain. -/
theorem continuousOn_radialProjection_of_separated {K L : Set Plane} {s : ℝ}
    (hs : 0 < s) (hsep : ∀ x ∈ K, ∀ y ∈ L, s ≤ dist x y) :
    ContinuousOn (Function.uncurry radialProjection) (K ×ˢ L) := by
  apply continuousOn_radialProjection.mono
  intro p hp
  exact (dist_pos.mp (hs.trans_le (hsep p.1 hp.1 p.2 hp.2)))

end FalconerThetaGauge
