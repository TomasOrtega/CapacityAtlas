/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteInformation.ObservationLaws

open scoped BigOperators

namespace CapacityAtlas.FiniteInformation

variable {Ω A B C : Type*} [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]

@[capacity_shared_api]
theorem information_sequence_prefix {n : ℕ} (p : FiniteDistribution Ω)
    (m : Ω → C) (f : Ω → Fin n → A) :
    information p m f = ∑ i : Fin n,
      conditional p m (fun ω ↦ f ω i) (sequencePrefix f i.val) := by
  have h := csiszar_sum_identity p m (fun _ ↦ ()) f (fun _ _ ↦ ())
  simp only [conditional_const, information_right_const, sub_zero,
    conditional_right_const] at h
  refine h.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  let k := fun v : Fin n → Option A ↦
    ((v, fun j : Fin n ↦ if i.val + 1 ≤ j.val then some () else none), ())
  change conditional p m (fun ω ↦ f ω i) (k ∘ sequencePrefix f i.val) = _
  exact conditional_condition_comp_injective p m _ _ k (by
    intro a b hab
    exact (Prod.mk.inj (Prod.mk.inj hab).1).1)

@[capacity_shared_api]
theorem information_sequence_suffix {n : ℕ} (p : FiniteDistribution Ω)
    (m : Ω → C) (g : Ω → Fin n → B) :
    information p m g = ∑ i : Fin n,
      conditional p m (fun ω ↦ g ω i) (sequenceSuffix g (i.val + 1)) := by
  have h := csiszar_sum_identity p m (fun _ ↦ ()) (fun _ _ ↦ ()) g
  simp only [conditional_const, information_right_const, zero_sub,
    conditional_right_const] at h
  have heq : (∑ i : Fin n,
      conditional p m (fun ω ↦ g ω i)
        (fun ω ↦ ((sequencePrefix (fun _ : Ω ↦ fun _ : Fin n ↦ ()) i.val ω,
          sequenceSuffix g (i.val + 1) ω), ()))) =
      ∑ i : Fin n, conditional p m (fun ω ↦ g ω i) (sequenceSuffix g (i.val + 1)) := by
    apply Finset.sum_congr rfl
    intro i _
    let k := fun v : Fin n → Option B ↦
      (((fun j : Fin n ↦ if j.val < i.val then some () else none), v), ())
    change conditional p m (fun ω ↦ g ω i) (k ∘ sequenceSuffix g (i.val + 1)) = _
    exact conditional_condition_comp_injective p m _ _ k (by
      intro a b hab
      exact (Prod.mk.inj (Prod.mk.inj hab).1).2)
  rw [Finset.sum_neg_distrib, heq] at h
  exact neg_injective h

@[capacity_shared_api]
theorem information_le_sum_common_prefix_suffix_left {n : ℕ}
    (p : FiniteDistribution Ω) (m : Ω → C)
    (f : Ω → Fin n → A) (g : Ω → Fin n → B) :
    information p m f ≤ ∑ i : Fin n,
      information p (fun ω ↦ (m ω, sequencePrefix f i.val ω,
        sequenceSuffix g (i.val + 1) ω)) (fun ω ↦ f ω i) := by
  rw [information_sequence_prefix]
  apply Finset.sum_le_sum
  intro i _
  apply (conditional_le_information_pair p m (fun ω ↦ f ω i) (sequencePrefix f i.val)).trans
  exact information_comp_left_le p
    (fun ω ↦ (m ω, sequencePrefix f i.val ω, sequenceSuffix g (i.val + 1) ω))
    (fun ω ↦ f ω i) (fun z ↦ (z.1, z.2.1))

@[capacity_shared_api]
theorem information_le_sum_common_prefix_suffix_right {n : ℕ}
    (p : FiniteDistribution Ω) (m : Ω → C)
    (f : Ω → Fin n → A) (g : Ω → Fin n → B) :
    information p m g ≤ ∑ i : Fin n,
      information p (fun ω ↦ (m ω, sequencePrefix f i.val ω,
        sequenceSuffix g (i.val + 1) ω)) (fun ω ↦ g ω i) := by
  rw [information_sequence_suffix]
  apply Finset.sum_le_sum
  intro i _
  apply (conditional_le_information_pair p m (fun ω ↦ g ω i)
    (sequenceSuffix g (i.val + 1))).trans
  exact information_comp_left_le p
    (fun ω ↦ (m ω, sequencePrefix f i.val ω, sequenceSuffix g (i.val + 1) ω))
    (fun ω ↦ g ω i) (fun z ↦ (z.1, z.2.2))

end CapacityAtlas.FiniteInformation
