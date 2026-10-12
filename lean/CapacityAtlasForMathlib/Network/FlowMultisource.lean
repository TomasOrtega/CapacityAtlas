/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Network.Flow

open scoped BigOperators

namespace CapacityAtlas.NetworkFlow

variable {V E I : Type*} [Fintype V] [Fintype E] [Fintype I]
  [DecidableEq V] [DecidableEq E] [DecidableEq I]

def augmentedSource (src : E → V) : I ⊕ E → Option V
  | .inl _ => none
  | .inr e => some (src e)

def augmentedTarget (supply : I → V) (dst : E → V) : I ⊕ E → Option V
  | .inl i => some (supply i)
  | .inr e => some (dst e)

def augmentedCapacity (cap : E → ℕ) : I ⊕ E → ℕ
  | .inl _ => 1
  | .inr e => cap e

omit [Fintype V] [Fintype E] [Fintype I] [DecidableEq V] [DecidableEq E]
  [DecidableEq I] in
theorem augmented_route_some (src dst : E → V) (supply : I → V) (s t : V)
    (es : List (I ⊕ E))
    (h : Route (augmentedSource src) (augmentedTarget supply dst) (some s) (some t) es) :
    ∃ l : List E, es = l.map Sum.inr ∧ Route src dst s t l := by
  induction es generalizing s with
  | nil => exact ⟨[], rfl, Option.some.inj h⟩
  | cons e es ih =>
    cases e with
    | inl i =>
      have hh : (none : Option V) = some s := h.1
      cases hh
    | inr e =>
      have hs : src e = s := Option.some.inj h.1
      obtain ⟨l, hl, hr⟩ := ih (dst e) h.2
      exact ⟨e :: l, by simp [hl], hs, hr⟩

omit [Fintype V] [Fintype E] [Fintype I] [DecidableEq V] [DecidableEq E]
  [DecidableEq I] in
theorem augmented_route_none (src dst : E → V) (supply : I → V) (t : V)
    (es : List (I ⊕ E))
    (h : Route (augmentedSource src) (augmentedTarget supply dst) none (some t) es) :
    ∃ i : I, ∃ l : List E, es = Sum.inl i :: l.map Sum.inr ∧
      Route src dst (supply i) t l := by
  cases es with
  | nil =>
    have hh : (none : Option V) = some t := h
    cases hh
  | cons e es =>
    cases e with
    | inr e =>
      have hh : some (src e) = (none : Option V) := h.1
      cases hh
    | inl i =>
      obtain ⟨l, hl, hr⟩ := augmented_route_some src dst supply (supply i) t es h.2
      exact ⟨i, l, by simp [hl], hr⟩

/-- Each independent input receives a route from its own source. -/
theorem multisource_route_packing (src dst : E → V) (supply : I → V) (cap : E → ℕ)
    (t : V) (hcut : ∀ S : Finset V, t ∉ S →
      (∑ i : I, if supply i ∈ S then 1 else 0) ≤ cutCapacity src dst cap S) :
    ∃ routes : I → List E,
      (∀ i, Route src dst (supply i) t (routes i) ∧ (routes i).Nodup) ∧
      ∀ e, (∑ i, (routes i).count e) ≤ cap e := by
  classical
  letI : BEq (I ⊕ E) := instBEqOfDecidableEq
  have haug : ∀ S : Finset (Option V), none ∈ S → some t ∉ S →
      Fintype.card I ≤ cutCapacity (augmentedSource (I := I) src)
        (augmentedTarget supply dst) (augmentedCapacity cap) S := by
    intro S hs ht
    let P := Finset.univ.filter (fun v : V ↦ some v ∈ S)
    have htP : t ∉ P := by simpa [P] using ht
    have hP := hcut P htP
    have hcount : (∑ i : I, if supply i ∈ P then 1 else 0) +
        (∑ i : I, if supply i ∈ P then 0 else 1) = Fintype.card I := by
      rw [← Finset.sum_add_distrib]
      have he : ∀ i : I, (if supply i ∈ P then 1 else 0) +
          (if supply i ∈ P then 0 else 1) = (1 : ℕ) := by intro i; split_ifs <;> rfl
      simp only [he, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
    have hval : cutCapacity (augmentedSource (I := I) src) (augmentedTarget supply dst)
        (augmentedCapacity cap) S =
        (∑ i : I, if supply i ∈ P then 0 else 1) + cutCapacity src dst cap P := by
      simp only [cutCapacity, Fintype.sum_sum_type, augmentedSource, augmentedTarget,
        augmentedCapacity, hs, true_and]
      simp [P, ite_not]
    rw [hval]
    omega
  obtain ⟨paths, hpaths, hbound⟩ := route_packing_of_cut
    (augmentedSource (I := I) src) (augmentedTarget supply dst) (augmentedCapacity cap)
    none (some t) (by simp) (Fintype.card I) haug
  have hp : ∀ j, ∃ i : I, ∃ l : List E,
      paths j = Sum.inl i :: l.map Sum.inr ∧ Route src dst (supply i) t l := by
    intro j
    exact augmented_route_none src dst supply t (paths j) (hpaths j).1
  choose input rest heq hr using hp
  have hcount : ∀ j, (paths j).count (Sum.inl (input j)) = 1 := by
    intro j
    rw [heq j, List.count_cons_self]
    have hz : (List.map (Sum.inr : E → I ⊕ E) (rest j)).count (Sum.inl (input j)) = 0 :=
      List.count_eq_zero.mpr (by simp)
    rw [hz]
  have hinj : Function.Injective input := by
    intro a b hab
    by_contra hne
    have htwo : (paths a).count (Sum.inl (input a)) +
        (paths b).count (Sum.inl (input a)) ≤
        ∑ j, (paths j).count (Sum.inl (input a)) := by
      simpa [hne] using
        (Finset.sum_le_sum_of_subset (f := fun j ↦ (paths j).count (Sum.inl (input a)))
          (show ({a, b} : Finset (Fin (Fintype.card I))) ⊆ Finset.univ from
            Finset.subset_univ _))
    have hb := hbound (Sum.inl (input a))
    rw [hcount a, hab, hcount b] at htwo
    rw [hab] at hb
    change _ ≤ 1 at hb
    omega
  let eqv : Fin (Fintype.card I) ≃ I := Equiv.ofBijective input
    ((Fintype.bijective_iff_injective_and_card input).mpr ⟨hinj, by simp⟩)
  refine ⟨fun i ↦ rest (eqv.symm i), ?_, ?_⟩
  · intro i
    constructor
    · have hi : input (eqv.symm i) = i := eqv.apply_symm_apply i
      simpa only [hi] using hr (eqv.symm i)
    · have h := (hpaths (eqv.symm i)).2
      rw [heq] at h
      exact List.Nodup.of_map Sum.inr (List.nodup_cons.mp h).2
  · intro e
    have hbe := hbound (Sum.inr e)
    change (∑ j, (paths j).count (Sum.inr e)) ≤ cap e at hbe
    have hcounts : ∀ j, (paths j).count (Sum.inr e) = (rest j).count e := by
      intro j
      rw [heq j, List.count_cons_of_ne (by simp)]
      exact List.count_map_of_injective _ Sum.inr Sum.inr_injective e
    have hb : (∑ j, (rest j).count e) ≤ cap e := by
      convert hbe using 1
      apply Finset.sum_congr rfl
      intro j _
      exact (hcounts j).symm
    change (∑ i, (rest (eqv.symm i)).count e) ≤ cap e
    rw [eqv.symm.sum_comp (fun j ↦ (rest j).count e)]
    exact hb

end CapacityAtlas.NetworkFlow
