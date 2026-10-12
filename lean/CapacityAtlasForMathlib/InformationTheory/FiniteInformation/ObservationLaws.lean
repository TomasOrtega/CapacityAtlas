/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteInformation.Identities

open scoped BigOperators

namespace CapacityAtlas.FiniteInformation

variable {Ω A B C D : Type*} [Fintype Ω] [Fintype A] [Fintype B]
  [Fintype C] [Fintype D]

@[capacity_shared_api]
theorem entropy_pair_const (p : FiniteDistribution Ω) (f : Ω → A) (b : B) :
    entropy p (fun ω ↦ (f ω, b)) = entropy p f :=
  entropy_comp_injective p f (fun a ↦ (a, b)) (fun _ _ h ↦ (Prod.mk.inj h).1)

@[capacity_shared_api]
theorem conditional_const (p : FiniteDistribution Ω) (f : Ω → A) (g : Ω → B) (c : C) :
    conditional p f g (fun _ ↦ c) = information p f g := by
  have htrip := entropy_comp_injective p (fun ω ↦ (f ω, g ω))
    (fun z ↦ (z.1, z.2, c)) (by
      intro a b h
      exact Prod.ext (Prod.mk.inj h).1 (Prod.mk.inj (Prod.mk.inj h).2).1)
  unfold conditional information
  rw [entropy_pair_const, entropy_pair_const, entropy_const]
  change _ - entropy p ((fun z : A × B ↦ (z.1, z.2, c)) ∘ (fun ω ↦ (f ω, g ω))) = _
  rw [htrip]
  ring

@[capacity_shared_api]
theorem conditional_right_const (p : FiniteDistribution Ω) (f : Ω → A)
    (g : Ω → C) (b : B) : conditional p f (fun _ ↦ b) g = 0 := by
  have htrip := entropy_comp_injective p (fun ω ↦ (f ω, g ω))
    (fun z ↦ (z.1, b, z.2)) (by
      intro a b h
      exact Prod.ext (Prod.mk.inj h).1 (Prod.mk.inj (Prod.mk.inj h).2).2)
  unfold conditional
  rw [entropy_pair_swap p (fun _ ↦ b) g, entropy_pair_const]
  change _ - entropy p ((fun z : A × C ↦ (z.1, b, z.2)) ∘ (fun ω ↦ (f ω, g ω))) = _
  rw [htrip]
  ring

@[capacity_shared_api]
theorem information_nonneg (p : FiniteDistribution Ω) (f : Ω → A) (g : Ω → B) :
    0 ≤ information p f g := by
  simpa only [conditional_const] using conditional_nonneg p f g (fun _ ↦ ())

@[capacity_shared_api]
theorem information_right_const (p : FiniteDistribution Ω) (f : Ω → A) (b : B) :
    information p f (fun _ ↦ b) = 0 := by
  simp only [information, entropy_const, entropy_pair_const]
  ring

@[capacity_shared_api]
theorem information_comp_left_injective (p : FiniteDistribution Ω)
    (f : Ω → A) (g : Ω → B) (k : A → C) (hk : Function.Injective k) :
    information p (k ∘ f) g = information p f g := by
  have hpair := entropy_comp_injective p (fun ω ↦ (f ω, g ω))
    (fun z ↦ (k z.1, z.2)) (by
      intro a b h
      exact Prod.ext (hk (Prod.mk.inj h).1) (Prod.mk.inj h).2)
  unfold information
  rw [entropy_comp_injective _ _ _ hk]
  exact congrArg (fun x ↦ entropy p f + entropy p g - x) hpair

@[capacity_shared_api]
theorem information_comp_left_le (p : FiniteDistribution Ω)
    (f : Ω → A) (g : Ω → B) (k : A → C) :
    information p (k ∘ f) g ≤ information p f g := by
  have hpair := information_comp_left_injective p f g (fun a ↦ (a, k a))
    (fun _ _ h ↦ (Prod.mk.inj h).1)
  have hchain := information_chain_rule p g f (k ∘ f)
  have hn := conditional_nonneg p g f (k ∘ f)
  rw [information_comm] at hpair
  simp only [Function.comp_def] at hpair hchain hn ⊢
  rw [← hpair, hchain, information_comm p (fun ω ↦ k (f ω)) g]
  exact le_add_of_nonneg_right hn

@[capacity_shared_api]
theorem conditional_le_information_pair (p : FiniteDistribution Ω)
    (f : Ω → A) (g : Ω → B) (h : Ω → C) :
    conditional p f g h ≤ information p (fun ω ↦ (f ω, h ω)) g := by
  rw [information_comm, information_chain_rule, conditional_comm p g f h]
  exact le_add_of_nonneg_left (information_nonneg p g h)

@[capacity_shared_api]
theorem conditional_condition_comp_injective (p : FiniteDistribution Ω)
    (f : Ω → A) (g : Ω → B) (h : Ω → C) (k : C → D) (hk : Function.Injective k) :
    conditional p f g (k ∘ h) = conditional p f g h := by
  have hfh := entropy_comp_injective p (fun ω ↦ (f ω, h ω))
    (fun z ↦ (z.1, k z.2)) (by
      intro a b h
      exact Prod.ext (Prod.mk.inj h).1 (hk (Prod.mk.inj h).2))
  have hgh := entropy_comp_injective p (fun ω ↦ (g ω, h ω))
    (fun z ↦ (z.1, k z.2)) (by
      intro a b h
      exact Prod.ext (Prod.mk.inj h).1 (hk (Prod.mk.inj h).2))
  have htrip := entropy_comp_injective p (fun ω ↦ (f ω, g ω, h ω))
    (fun z ↦ (z.1, z.2.1, k z.2.2)) (by
      intro a b hab
      exact Prod.ext (Prod.mk.inj hab).1 (Prod.ext (Prod.mk.inj (Prod.mk.inj hab).2).1
        (hk (Prod.mk.inj (Prod.mk.inj hab).2).2)))
  unfold conditional
  rw [entropy_comp_injective _ _ _ hk]
  simp only [Function.comp_def] at hfh hgh htrip ⊢
  rw [hfh, hgh, htrip]

end CapacityAtlas.FiniteInformation
