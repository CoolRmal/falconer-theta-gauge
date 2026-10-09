/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerThetaGauge.GaugeFrostmanDyadic

/-!
# Finite dyadic Frostman normalization for positive capacities

Adapted from `FalconerPacking.FrostmanWeights` (original attribution preserved above),
`CoolRmal/falconer-packing` commit `70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/blob/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking/FrostmanWeights.lean
The construction is generalized from power allowances to any positive sequence
of capacities. Starting with the finest capacity, it repeatedly scales down
weights in overfull ancestors. Every generation satisfies its capacity, every
occupied finest cube retains a saturated ancestor, and maximal saturated cubes
have disjoint fibres whose capacities sum to at most the remaining total mass.
-/

@[expose] public section

noncomputable section

open Finset

namespace FalconerThetaGauge.GaugeFrostman

/-- The positive capacity prescribed at each dyadic generation. -/
structure PositiveCapacity where
  value : ℕ → ℝ
  positive : ∀ j, 0 < value j

variable (S : Finset (Fin 2 → ℤ)) (n : ℕ) (d : PositiveCapacity)

/-- The capacity of a generation-`j` cube. -/
def allowance (j : ℕ) (d : PositiveCapacity) : ℝ := d.value j

theorem allowance_pos (j : ℕ) (d : PositiveCapacity) : 0 < allowance j d :=
  d.positive j

/-- The mass of the generation-`j` cube with index `k`, for weights carried by generation-`n`
cubes. -/
def cubeMass (S : Finset (Fin 2 → ℤ)) (n j : ℕ) (w : (Fin 2 → ℤ) → ℝ) (k : Fin 2 → ℤ) : ℝ :=
  ∑ k' ∈ S.filter fun k' ↦ ancestor (n - j) k' = k, w k'

theorem cubeMass_nonneg {w : (Fin 2 → ℤ) → ℝ} (hw : ∀ k, 0 ≤ w k) (j : ℕ) (k : Fin 2 → ℤ) :
    0 ≤ cubeMass S n j w k :=
  Finset.sum_nonneg fun k' _ ↦ hw k'

theorem cubeMass_mono {w w' : (Fin 2 → ℤ) → ℝ} (h : ∀ k, w k ≤ w' k) (j : ℕ) (k : Fin 2 → ℤ) :
    cubeMass S n j w k ≤ cubeMass S n j w' k :=
  Finset.sum_le_sum fun k' _ ↦ h k'

/-- One normalization step at generation `j`: scale each weight by the factor attached to its
generation-`j` ancestor, so that the cube's mass falls to its allowance. -/
def normalizeStep (S : Finset (Fin 2 → ℤ)) (n j : ℕ) (d : PositiveCapacity) (w : (Fin 2 → ℤ) → ℝ) :
    (Fin 2 → ℤ) → ℝ := fun k' ↦
  if cubeMass S n j w (ancestor (n - j) k') ≤ allowance j d then w k'
  else w k' * (allowance j d / cubeMass S n j w (ancestor (n - j) k'))

theorem normalizeStep_nonneg {w : (Fin 2 → ℤ) → ℝ} (hw : ∀ k, 0 ≤ w k) (j : ℕ)
    (k' : Fin 2 → ℤ) : 0 ≤ normalizeStep S n j d w k' := by
  rw [normalizeStep]
  split
  · exact hw k'
  · rename_i hcon
    rw [not_le] at hcon
    have hm : 0 < cubeMass S n j w (ancestor (n - j) k') := (allowance_pos j d).trans hcon
    exact mul_nonneg (hw k') (div_nonneg (allowance_pos j d).le hm.le)

/-- The step never increases a weight. -/
theorem normalizeStep_le {w : (Fin 2 → ℤ) → ℝ} (hw : ∀ k, 0 ≤ w k) (j : ℕ) (k' : Fin 2 → ℤ) :
    normalizeStep S n j d w k' ≤ w k' := by
  rw [normalizeStep]
  split
  · exact le_rfl
  · rename_i hcon
    rw [not_le] at hcon
    have hm : 0 < cubeMass S n j w (ancestor (n - j) k') := (allowance_pos j d).trans hcon
    refine mul_le_of_le_one_right (hw k') ?_
    rw [div_le_one hm]
    exact hcon.le

/-- **The step enforces the allowance.**  After normalizing at generation `j`, every
generation-`j` cube has mass at most its prescribed capacity. -/
theorem cubeMass_normalizeStep_le {w : (Fin 2 → ℤ) → ℝ} (_hw : ∀ k, 0 ≤ w k) (j : ℕ)
    (k : Fin 2 → ℤ) :
    cubeMass S n j (normalizeStep S n j d w) k ≤ allowance j d := by
  by_cases hle : cubeMass S n j w k ≤ allowance j d
  · refine le_trans (le_of_eq ?_) hle
    refine Finset.sum_congr rfl fun k' hk' ↦ ?_
    have hanc : ancestor (n - j) k' = k := (Finset.mem_filter.1 hk').2
    rw [normalizeStep, hanc, ite_eq_left hle]
  · rw [not_le] at hle
    have hm : 0 < cubeMass S n j w k := (allowance_pos j d).trans hle
    have hsum : cubeMass S n j (normalizeStep S n j d w) k
        = cubeMass S n j w k * (allowance j d / cubeMass S n j w k) := by
      rw [cubeMass, cubeMass, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k' hk' ↦ ?_
      have hanc : ancestor (n - j) k' = k := (Finset.mem_filter.1 hk').2
      rw [normalizeStep, hanc, ite_eq_right (not_le.2 hle), cubeMass]
    rw [hsum, mul_div_cancel₀ _ hm.ne']

/-- The normalization walk: process generations `j, j - 1, …, 0` in that order. -/
def normalizeDown (S : Finset (Fin 2 → ℤ)) (n : ℕ) (d : PositiveCapacity) :
    ℕ → ((Fin 2 → ℤ) → ℝ) → ((Fin 2 → ℤ) → ℝ)
  | 0, w => normalizeStep S n 0 d w
  | (j + 1), w => normalizeDown S n d j (normalizeStep S n (j + 1) d w)

theorem normalizeDown_nonneg :
    ∀ (j : ℕ) {w : (Fin 2 → ℤ) → ℝ}, (∀ k, 0 ≤ w k) → ∀ k, 0 ≤ normalizeDown S n d j w k
  | 0, _, hw => normalizeStep_nonneg S n d hw 0
  | (j + 1), _, hw =>
      normalizeDown_nonneg j (normalizeStep_nonneg S n d hw (j + 1))

/-- The walk never increases a weight. -/
theorem normalizeDown_le :
    ∀ (j : ℕ) {w : (Fin 2 → ℤ) → ℝ}, (∀ k, 0 ≤ w k) → ∀ k, normalizeDown S n d j w k ≤ w k
  | 0, w, hw => normalizeStep_le S n d hw 0
  | (j + 1), w, hw => by
      intro k
      refine le_trans (normalizeDown_le j (normalizeStep_nonneg S n d hw (j + 1)) k) ?_
      exact normalizeStep_le S n d hw (j + 1) k

/-- **The Frostman property of the construction.**  After walking down from generation `j`,
every generation `i ≤ j` obeys its allowance. -/
theorem cubeMass_normalizeDown_le :
    ∀ (j : ℕ) {w : (Fin 2 → ℤ) → ℝ}, (∀ k, 0 ≤ w k) → ∀ i ≤ j, ∀ k,
      cubeMass S n i (normalizeDown S n d j w) k ≤ allowance i d
  | 0, w, hw => by
      intro i hi k
      have hi0 : i = 0 := Nat.le_zero.1 hi
      subst hi0
      exact cubeMass_normalizeStep_le S n d hw 0 k
  | (j + 1), w, hw => by
      intro i hi k
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · exact cubeMass_normalizeDown_le j (normalizeStep_nonneg S n d hw (j + 1)) i
          (by omega) k
      · have hij : i = j + 1 := by omega
        subst hij
        refine le_trans (cubeMass_mono S n ?_ (j + 1) k)
          (cubeMass_normalizeStep_le S n d hw (j + 1) k)
        intro k'
        exact normalizeDown_le S n d j (normalizeStep_nonneg S n d hw (j + 1)) k'

section Saturation

variable {S n d}

/-- At the finest generation the mass of a cube is just the weight it carries. -/
theorem cubeMass_self (w : (Fin 2 → ℤ) → ℝ) (k : Fin 2 → ℤ) :
    cubeMass S n n w k = if k ∈ S then w k else 0 := by
  classical
  rw [cubeMass, Nat.sub_self]
  by_cases hk : k ∈ S
  · rw [ite_eq_left hk]
    refine Finset.sum_eq_single_of_mem k ?_ ?_
    · exact Finset.mem_filter.2 ⟨hk, by simp⟩
    · intro b hb hbk
      have : ancestor 0 b = k := (Finset.mem_filter.1 hb).2
      rw [ancestor_zero] at this
      exact absurd this hbk
  · rw [ite_eq_right hk]
    refine Finset.sum_eq_zero fun b hb ↦ ?_
    have hbS : b ∈ S := (Finset.mem_filter.1 hb).1
    have hbk : ancestor 0 b = k := (Finset.mem_filter.1 hb).2
    rw [ancestor_zero] at hbk
    exact absurd (hbk ▸ hbS) hk

/-- The initial weights of the construction: every occupied cube of generation `n` carries its
own allowance. -/
def initialWeight (n : ℕ) (d : PositiveCapacity) : (Fin 2 → ℤ) → ℝ := fun _ ↦ allowance n d

theorem initialWeight_nonneg (n : ℕ) (d : PositiveCapacity) (k : Fin 2 → ℤ) : 0 ≤ initialWeight n d k :=
  (allowance_pos n d).le

/-- The initial weights saturate every occupied cube of the finest generation. -/
theorem cubeMass_initialWeight (S : Finset (Fin 2 → ℤ)) (n : ℕ) (d : PositiveCapacity) {k : Fin 2 → ℤ}
    (hk : k ∈ S) : cubeMass S n n (initialWeight n d) k = allowance n d := by
  rw [cubeMass_self, ite_eq_left hk, initialWeight]

/-- **The step dichotomy.**  At each generation a cube is either left untouched by the
normalization, or it is saturated: its mass becomes exactly its allowance.  This is what makes
the saturated cubes of the finished walk a cover of the set. -/
theorem normalizeStep_dichotomy (w : (Fin 2 → ℤ) → ℝ) (j : ℕ) (k : Fin 2 → ℤ) :
    (∀ k' ∈ S.filter fun k' ↦ ancestor (n - j) k' = k, normalizeStep S n j d w k' = w k')
      ∨ cubeMass S n j (normalizeStep S n j d w) k = allowance j d := by
  by_cases hle : cubeMass S n j w k ≤ allowance j d
  · refine Or.inl fun k' hk' ↦ ?_
    have hanc : ancestor (n - j) k' = k := (Finset.mem_filter.1 hk').2
    rw [normalizeStep, hanc, ite_eq_left hle]
  · refine Or.inr ?_
    rw [not_le] at hle
    have hm : 0 < cubeMass S n j w k := (allowance_pos j d).trans hle
    have hsum : cubeMass S n j (normalizeStep S n j d w) k
        = cubeMass S n j w k * (allowance j d / cubeMass S n j w k) := by
      rw [cubeMass, cubeMass, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k' hk' ↦ ?_
      have hanc : ancestor (n - j) k' = k := (Finset.mem_filter.1 hk').2
      rw [normalizeStep, hanc, ite_eq_right (not_le.2 hle), cubeMass]
    rw [hsum, mul_div_cancel₀ _ hm.ne']

end Saturation

section Invariant

variable {S n d}

/-- Inside an untouched cube, the masses of all finer cubes are unchanged. -/
theorem cubeMass_eq_of_untouched {w w' : (Fin 2 → ℤ) → ℝ} {j i : ℕ} (hji : j ≤ i) (hin : i ≤ n)
    {Q : Fin 2 → ℤ} (h : ∀ k' ∈ S.filter fun k' ↦ ancestor (n - j) k' = Q, w' k' = w k')
    {c : Fin 2 → ℤ} (hc : ancestor (i - j) c = Q) :
    cubeMass S n i w' c = cubeMass S n i w c := by
  refine Finset.sum_congr rfl fun k' hk' ↦ ?_
  have hanc : ancestor (n - i) k' = c := (Finset.mem_filter.1 hk').2
  have hS : k' ∈ S := (Finset.mem_filter.1 hk').1
  refine h k' (Finset.mem_filter.2 ⟨hS, ?_⟩)
  have harith : i - j + (n - i) = n - j := by omega
  rw [← harith, ← ancestor_ancestor, hanc, hc]

/-- The walk's invariant: every occupied cube of the finest generation has an ancestor, at some
generation above `j`, whose mass is exactly its allowance. -/
def SaturatedAbove (S : Finset (Fin 2 → ℤ)) (n : ℕ) (d : PositiveCapacity) (w : (Fin 2 → ℤ) → ℝ) (j : ℕ) :
    Prop :=
  ∀ k' ∈ S, ∃ i, j < i ∧ i ≤ n ∧ cubeMass S n i w (ancestor (n - i) k') = allowance i d

/-- The conclusion of the walk: every occupied cube has a saturated ancestor. -/
def SaturatedSomewhere (S : Finset (Fin 2 → ℤ)) (n : ℕ) (d : PositiveCapacity) (w : (Fin 2 → ℤ) → ℝ) : Prop :=
  ∀ k' ∈ S, ∃ i ≤ n, cubeMass S n i w (ancestor (n - i) k') = allowance i d

/-- A step at generation `j + 1` lowers the invariant by one generation: cubes it scales become
saturated there, and cubes it leaves alone keep their finer saturation. -/
theorem saturatedAbove_normalizeStep {w : (Fin 2 → ℤ) → ℝ} {j : ℕ} (hj : j + 1 ≤ n)
    (h : SaturatedAbove S n d w (j + 1)) :
    SaturatedAbove S n d (normalizeStep S n (j + 1) d w) j := by
  intro k' hk'
  rcases normalizeStep_dichotomy (S := S) (n := n) (d := d) w (j + 1)
    (ancestor (n - (j + 1)) k') with huntouched | hsat
  · obtain ⟨i, hij, hin, hmass⟩ := h k' hk'
    refine ⟨i, by omega, hin, ?_⟩
    have hc : ancestor (i - (j + 1)) (ancestor (n - i) k') = ancestor (n - (j + 1)) k' := by
      rw [ancestor_ancestor]
      congr 1
      omega
    rw [cubeMass_eq_of_untouched (by omega) hin huntouched hc]
    exact hmass
  · exact ⟨j + 1, by omega, hj, hsat⟩

/-- The final step, at generation `0`. -/
theorem saturatedSomewhere_normalizeStep_zero {w : (Fin 2 → ℤ) → ℝ}
    (h : SaturatedAbove S n d w 0) :
    SaturatedSomewhere S n d (normalizeStep S n 0 d w) := by
  intro k' hk'
  rcases normalizeStep_dichotomy (S := S) (n := n) (d := d) w 0
    (ancestor (n - 0) k') with huntouched | hsat
  · obtain ⟨i, hij, hin, hmass⟩ := h k' hk'
    refine ⟨i, hin, ?_⟩
    have hc : ancestor (i - 0) (ancestor (n - i) k') = ancestor (n - 0) k' := by
      rw [ancestor_ancestor]
      congr 1
      omega
    rw [cubeMass_eq_of_untouched (by omega) hin huntouched hc]
    exact hmass
  · exact ⟨0, Nat.zero_le n, hsat⟩

/-- **The walk saturates every occupied cube.** -/
theorem saturatedSomewhere_normalizeDown :
    ∀ (j : ℕ), j ≤ n → ∀ {w : (Fin 2 → ℤ) → ℝ}, SaturatedAbove S n d w j →
      SaturatedSomewhere S n d (normalizeDown S n d j w)
  | 0, _, w, h => saturatedSomewhere_normalizeStep_zero h
  | (j + 1), hj, w, h => by
      refine saturatedSomewhere_normalizeDown j (by omega) ?_
      exact saturatedAbove_normalizeStep (by omega) h

/-- The initial weights satisfy the invariant at the finest generation. -/
theorem saturatedAbove_initialWeight (S : Finset (Fin 2 → ℤ)) {n : ℕ} (hn : 1 ≤ n) (d : PositiveCapacity) :
    SaturatedAbove S n d (initialWeight n d) (n - 1) := by
  intro k' hk'
  refine ⟨n, by omega, le_rfl, ?_⟩
  rw [Nat.sub_self, ancestor_zero]
  exact cubeMass_initialWeight S n d hk'

/-- **The finished walk.**  Starting from the initial weights, the normalization leaves every
occupied cube with a saturated ancestor, while every generation stays within its allowance. -/
theorem saturatedSomewhere_frostmanWeights (S : Finset (Fin 2 → ℤ)) {n : ℕ} (hn : 1 ≤ n)
    (d : PositiveCapacity) :
    SaturatedSomewhere S n d (normalizeDown S n d (n - 1) (initialWeight n d)) :=
  saturatedSomewhere_normalizeDown (n - 1) (by omega) (saturatedAbove_initialWeight S hn d)

end Invariant

section MaximalSaturated

variable {S n d}

open Classical in
/-- The coarsest generation at which the ancestor of an occupied cube is saturated. -/
noncomputable def satLevel (S : Finset (Fin 2 → ℤ)) (n : ℕ) (d : PositiveCapacity) (w : (Fin 2 → ℤ) → ℝ)
    (k' : Fin 2 → ℤ) : ℕ :=
  if h : ∃ i, i ≤ n ∧ cubeMass S n i w (ancestor (n - i) k') = allowance i d then Nat.find h else 0

/-- Saturation is inherited: if a cube is saturated, its generation is a saturation level of
every finest cube inside it. -/
theorem sat_of_mem {w : (Fin 2 → ℤ) → ℝ} {i : ℕ} {c k' : Fin 2 → ℤ} (hin : i ≤ n)
    (hanc : ancestor (n - i) k' = c) (hc : cubeMass S n i w c = allowance i d) :
    ∃ j, j ≤ n ∧ cubeMass S n j w (ancestor (n - j) k') = allowance j d :=
  ⟨i, hin, by rw [hanc]; exact hc⟩

theorem satLevel_le {w : (Fin 2 → ℤ) → ℝ} {k' : Fin 2 → ℤ}
    (h : ∃ i, i ≤ n ∧ cubeMass S n i w (ancestor (n - i) k') = allowance i d) :
    satLevel S n d w k' ≤ n := by
  classical
  rw [satLevel, dite_eq_left h]
  exact (Nat.find_spec h).1

theorem cubeMass_satLevel {w : (Fin 2 → ℤ) → ℝ} {k' : Fin 2 → ℤ}
    (h : ∃ i, i ≤ n ∧ cubeMass S n i w (ancestor (n - i) k') = allowance i d) :
    cubeMass S n (satLevel S n d w k') w (ancestor (n - satLevel S n d w k') k')
      = allowance (satLevel S n d w k') d := by
  classical
  rw [satLevel, dite_eq_left h]
  exact (Nat.find_spec h).2

theorem satLevel_min {w : (Fin 2 → ℤ) → ℝ} {k' : Fin 2 → ℤ} {i : ℕ}
    (h : ∃ i, i ≤ n ∧ cubeMass S n i w (ancestor (n - i) k') = allowance i d) (hin : i ≤ n)
    (hi : cubeMass S n i w (ancestor (n - i) k') = allowance i d) :
    satLevel S n d w k' ≤ i := by
  classical
  rw [satLevel, dite_eq_left h]
  exact Nat.find_min' h ⟨hin, hi⟩

/-- The maximal saturated cube of an occupied cube: its coarsest saturated ancestor. -/
noncomputable def satCube (S : Finset (Fin 2 → ℤ)) (n : ℕ) (d : PositiveCapacity) (w : (Fin 2 → ℤ) → ℝ)
    (k' : Fin 2 → ℤ) : ℕ × (Fin 2 → ℤ) :=
  (satLevel S n d w k', ancestor (n - satLevel S n d w k') k')

/-- **The maximal saturated cubes are disjoint.**  Two of them that share a finest cube are
equal: each contains the other's generator, so minimality of the saturation level forces the
generations to agree. -/
theorem satCube_eq_of_mem {w : (Fin 2 → ℤ) → ℝ} (hsat : SaturatedSomewhere S n d w)
    {a b k' : Fin 2 → ℤ} (ha : a ∈ S) (hb : b ∈ S) (hk' : k' ∈ S)
    (hka : ancestor (n - (satCube S n d w a).1) k' = (satCube S n d w a).2)
    (hkb : ancestor (n - (satCube S n d w b).1) k' = (satCube S n d w b).2) :
    satCube S n d w a = satCube S n d w b := by
  have hex : ∀ c ∈ S, ∃ i, i ≤ n ∧ cubeMass S n i w (ancestor (n - i) c) = allowance i d :=
    fun c hc ↦ (hsat c hc).imp fun i hi ↦ ⟨hi.1, hi.2⟩
  -- both cubes are saturated, so both generations are saturation levels of `k'`
  have hsatA : cubeMass S n (satCube S n d w a).1 w (satCube S n d w a).2
      = allowance (satCube S n d w a).1 d := cubeMass_satLevel (hex a ha)
  have hsatB : cubeMass S n (satCube S n d w b).1 w (satCube S n d w b).2
      = allowance (satCube S n d w b).1 d := cubeMass_satLevel (hex b hb)
  have hkA : satLevel S n d w k' ≤ (satCube S n d w a).1 :=
    satLevel_min (hex k' hk') (satLevel_le (hex a ha)) (by rw [hka]; exact hsatA)
  have hkB : satLevel S n d w k' ≤ (satCube S n d w b).1 :=
    satLevel_min (hex k' hk') (satLevel_le (hex b hb)) (by rw [hkb]; exact hsatB)
  -- the coarsest saturated cube of `k'` contains both, so it saturates their generators too
  have hcontains : ∀ {c : Fin 2 → ℤ}, c ∈ S →
      ancestor (n - (satCube S n d w c).1) k' = (satCube S n d w c).2 →
      satLevel S n d w k' ≤ (satCube S n d w c).1 →
      (satCube S n d w c).1 ≤ satLevel S n d w k' := by
    intro c hc hkc hle
    have hanc : ancestor (n - satLevel S n d w k') c
        = ancestor (n - satLevel S n d w k') k' := by
      have h1 : ancestor ((satCube S n d w c).1 - satLevel S n d w k')
          (ancestor (n - (satCube S n d w c).1) c) = ancestor (n - satLevel S n d w k') c := by
        rw [ancestor_ancestor]
        congr 1
        have hfst : (satCube S n d w c).1 = satLevel S n d w c := rfl
        have := satLevel_le (hex c hc)
        omega
      have h2 : ancestor ((satCube S n d w c).1 - satLevel S n d w k')
          (ancestor (n - (satCube S n d w c).1) k') = ancestor (n - satLevel S n d w k') k' := by
        rw [ancestor_ancestor]
        congr 1
        have hfst : (satCube S n d w c).1 = satLevel S n d w c := rfl
        have := satLevel_le (hex c hc)
        omega
      rw [← h1, ← h2, hkc]
      rfl
    refine satLevel_min (hex c hc) (satLevel_le (hex k' hk')) ?_
    rw [hanc]
    exact cubeMass_satLevel (hex k' hk')
  have hA := hcontains ha hka hkA
  have hB := hcontains hb hkb hkB
  have hlevels : (satCube S n d w a).1 = (satCube S n d w b).1 := by omega
  refine Prod.ext hlevels ?_
  rw [← hka, ← hkb, hlevels]

end MaximalSaturated

section MassBound

variable {S n d}

/-- The maximal saturated cubes of the occupied cubes. -/
noncomputable def satCubes (S : Finset (Fin 2 → ℤ)) (n : ℕ) (d : PositiveCapacity) (w : (Fin 2 → ℤ) → ℝ) :
    Finset (ℕ × (Fin 2 → ℤ)) :=
  S.image (satCube S n d w)

/-- **The saturated cubes carry no more than the total mass.**  Their fibres are disjoint, so
their allowances sum to at most the total weight. -/
theorem sum_allowance_satCubes_le {w : (Fin 2 → ℤ) → ℝ} (hsat : SaturatedSomewhere S n d w)
    (hw : ∀ k, 0 ≤ w k) :
    ∑ p ∈ satCubes S n d w, allowance p.1 d ≤ ∑ k' ∈ S, w k' := by
  classical
  have hex : ∀ c ∈ S, ∃ i, i ≤ n ∧ cubeMass S n i w (ancestor (n - i) c) = allowance i d :=
    fun c hc ↦ (hsat c hc).imp fun i hi ↦ ⟨hi.1, hi.2⟩
  set fibre : ℕ × (Fin 2 → ℤ) → Finset (Fin 2 → ℤ) :=
    fun p ↦ S.filter fun k' ↦ ancestor (n - p.1) k' = p.2 with hfibre
  have hsatmass : ∀ p ∈ satCubes S n d w, allowance p.1 d = ∑ k' ∈ fibre p, w k' := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hp
    exact (cubeMass_satLevel (hex a ha)).symm
  have hdisj : (satCubes S n d w : Set (ℕ × (Fin 2 → ℤ))).PairwiseDisjoint fibre := by
    intro p hp q hq hpq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hq
    refine Finset.disjoint_left.2 fun k' hk'p hk'q ↦ hpq ?_
    have hk'S : k' ∈ S := (Finset.mem_filter.1 hk'p).1
    exact satCube_eq_of_mem hsat ha hb hk'S (Finset.mem_filter.1 hk'p).2
      (Finset.mem_filter.1 hk'q).2
  calc ∑ p ∈ satCubes S n d w, allowance p.1 d
      = ∑ p ∈ satCubes S n d w, ∑ k' ∈ fibre p, w k' :=
        Finset.sum_congr rfl hsatmass
    _ = ∑ k' ∈ (satCubes S n d w).biUnion fibre, w k' := (Finset.sum_biUnion hdisj).symm
    _ ≤ ∑ k' ∈ S, w k' := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k' _ _ ↦ hw k'
        intro k' hk'
        obtain ⟨p, _, hk'p⟩ := Finset.mem_biUnion.1 hk'
        exact (Finset.mem_filter.1 hk'p).1

/-- Every occupied cube lies inside its maximal saturated ancestor. -/
theorem dyadicCube_subset_satCube {w : (Fin 2 → ℤ) → ℝ} (hsat : SaturatedSomewhere S n d w)
    {k' : Fin 2 → ℤ} (hk' : k' ∈ S) :
    dyadicCube n k' ⊆ dyadicCube (satCube S n d w k').1 (satCube S n d w k').2 := by
  have hex : ∃ i, i ≤ n ∧ cubeMass S n i w (ancestor (n - i) k') = allowance i d :=
    (hsat k' hk').imp fun i hi ↦ ⟨hi.1, hi.2⟩
  have hle : satLevel S n d w k' ≤ n := satLevel_le hex
  have harith : satLevel S n d w k' + (n - satLevel S n d w k') = n := by omega
  have := dyadicCube_subset_ancestor (satLevel S n d w k') (n - satLevel S n d w k') k'
  rw [harith] at this
  exact this

end MassBound

/-- Finite gauge Frostman normalization. It constructs nonnegative weights with
all generation bounds and a coarser cover whose capacity cost is controlled by
those weights. The construction applies to every positive capacity sequence. -/
theorem exists_capacity_weights (S : Finset (Fin 2 → ℤ)) {n : ℕ} (hn : 1 ≤ n)
    (d : PositiveCapacity) {E : Set Plane} (hcov : E ⊆ ⋃ k' ∈ S, dyadicCube n k') :
    ∃ (w : (Fin 2 → ℤ) → ℝ) (F : Finset (ℕ × (Fin 2 → ℤ))),
      (∀ k, 0 ≤ w k) ∧
      (∀ i ≤ n, ∀ k, cubeMass S n i w k ≤ allowance i d) ∧
      (∀ p ∈ F, p.1 ≤ n) ∧
      (E ⊆ ⋃ p ∈ F, dyadicCube p.1 p.2) ∧
      (∑ p ∈ F, allowance p.1 d ≤ ∑ k' ∈ S, w k') := by
  classical
  let w := normalizeDown S n d (n - 1) (initialWeight n d)
  have hinit : ∀ k, 0 ≤ initialWeight n d k := initialWeight_nonneg n d
  have hwnonneg : ∀ k, 0 ≤ w k := normalizeDown_nonneg S n d (n - 1) hinit
  have hsat : SaturatedSomewhere S n d w := saturatedSomewhere_frostmanWeights S hn d
  refine ⟨w, satCubes S n d w, hwnonneg, ?_, ?_, ?_, sum_allowance_satCubes_le hsat hwnonneg⟩
  · intro i hi k
    rcases Nat.lt_or_ge i n with hlt | hge
    · exact cubeMass_normalizeDown_le S n d (n - 1) hinit i (by omega) k
    · have hin : i = n := by omega
      rw [hin, cubeMass_self]
      split
      · exact (normalizeDown_le S n d (n - 1) hinit k).trans_eq rfl
      · exact (allowance_pos n d).le
  · intro p hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
    exact satLevel_le (hsat k hk)
  · intro x hx
    obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp (hcov hx)
    exact Set.mem_iUnion₂.mpr ⟨satCube S n d w k, Finset.mem_image.mpr ⟨k, hk, rfl⟩,
      dyadicCube_subset_satCube hsat hk hxk⟩

end FalconerThetaGauge.GaugeFrostman
