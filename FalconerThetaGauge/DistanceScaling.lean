module

public import FalconerThetaGauge.GaugeSeparatedMeasuresSimilarity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Transfer of positive distance-set length under preparation

The positive affine similarity used in Proposition 5.6 multiplies every
distance and the Lebesgue measure of the distance image by the same factor.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerThetaGauge

open GaugeSeparatedMeasures

/-- Preparation scales the exact all-pairs distance image. -/
theorem distanceSet_affineMap_image {ℓ : ℝ} (hℓ : 0 < ℓ) (z : Plane) (E : Set Plane) :
    distanceSet (affineMap ℓ z '' E) = (fun r : ℝ ↦ ℓ * r) '' distanceSet E := by
  ext r
  constructor
  · rintro ⟨⟨x, y⟩, ⟨⟨u, hu, rfl⟩, ⟨v, hv, rfl⟩⟩, rfl⟩
    exact ⟨dist u v, ⟨(u, v), ⟨hu, hv⟩, rfl⟩, (affineMap_dist hℓ z u v).symm⟩
  · rintro ⟨r, ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩, rfl⟩
    exact ⟨(affineMap ℓ z x, affineMap ℓ z y),
      ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩, affineMap_dist hℓ z x y⟩

/-- A positive real dilation scales the Lebesgue outer measure of every set. -/
theorem volume_image_positive_mul {ℓ : ℝ} (hℓ : 0 < ℓ) (A : Set ℝ) :
    volume ((fun r : ℝ ↦ ℓ * r) '' A) = ENNReal.ofReal ℓ * volume A := by
  have heq : (fun r : ℝ ↦ ℓ * r) '' A = (fun r : ℝ ↦ ℓ⁻¹ * r) ⁻¹' A := by
    ext r
    constructor
    · rintro ⟨s, hs, rfl⟩
      simpa only [mem_preimage, ← mul_assoc, inv_mul_cancel₀ hℓ.ne', one_mul] using hs
    · intro hr
      exact ⟨ℓ⁻¹ * r, hr, by simp [hℓ.ne']⟩
  rw [heq, Real.volume_preimage_mul_left (inv_ne_zero hℓ.ne')]
  simp only [inv_inv, abs_of_pos hℓ]

/-- The distance-set length scales exactly under the prepared similarity. -/
theorem volume_distanceSet_affineMap_image {ℓ : ℝ} (hℓ : 0 < ℓ)
    (z : Plane) (E : Set Plane) :
    volume (distanceSet (affineMap ℓ z '' E)) = ENNReal.ofReal ℓ * volume (distanceSet E) := by
  rw [distanceSet_affineMap_image hℓ, volume_image_positive_mul hℓ]

/-- Positive length obtained for the prepared copy transfers back to the source. -/
theorem volume_distanceSet_affineMap_image_pos_iff {ℓ : ℝ} (hℓ : 0 < ℓ)
    (z : Plane) (E : Set Plane) :
    0 < volume (distanceSet (affineMap ℓ z '' E)) ↔ 0 < volume (distanceSet E) := by
  rw [volume_distanceSet_affineMap_image hℓ]
  simp only [ENNReal.mul_pos_iff, ENNReal.ofReal_pos, hℓ, true_and]

end FalconerThetaGauge
