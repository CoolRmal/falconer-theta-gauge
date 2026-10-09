module

public import FalconerThetaGauge.RadialProjectionDefinitions

/-!
# Polar integration in the Euclidean plane

The exact Jacobian formula is transferred from Mathlib's complex polar coordinates
by the volume-preserving standard real linear isometry. The transfer follows
`FalconerPacking.PolarFourierEnergy` (original source credits Yongxi Lin, Apache 2.0),
at commit `70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/blob/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking/PolarFourierEnergy.lean
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerThetaGauge

/-- Exact polar integration, with unnormalized angular arc length and radial Jacobian `r`. -/
theorem lintegral_polar_euclidean (f : Plane → ℝ≥0∞) :
    ∫⁻ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal p.1 * f (p.1 • angularDirection p.2) = ∫⁻ x, f x := by
  have h := Complex.lintegral_comp_polarCoord_symm
    (fun z ↦ f (Complex.orthonormalBasisOneI.repr z))
  have he := Complex.orthonormalBasisOneI.repr.measurePreserving.lintegral_comp_emb
    Complex.orthonormalBasisOneI.repr.toHomeomorph.measurableEmbedding f
  rw [he] at h
  simpa only [polarCoord_target, Complex.polarCoord_symm_apply,
    angularDirection, ← Complex.real_smul, map_smul, smul_eq_mul] using h

end FalconerThetaGauge
