/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteInformation.Identities

open scoped BigOperators

namespace CapacityAtlas.FiniteDistribution

variable {A B : Type*} [Fintype A] [Fintype B]

@[capacity_shared_api]
theorem map_fst_apply [DecidableEq A] (p : FiniteDistribution (A × B)) (a : A) :
    p.map Prod.fst a = ∑ b, p (a, b) := by
  classical
  change (∑ z with z.1 = a, p z) = _
  simp only [Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp

@[capacity_shared_api]
theorem apply_eq_zero_of_map_fst_eq_zero [DecidableEq A]
    (p : FiniteDistribution (A × B)) {a : A} (ha : p.map Prod.fst a = 0) (b : B) :
    p (a, b) = 0 := by
  apply le_antisymm _ (p.nonnegative _)
  rw [map_fst_apply] at ha
  calc
    p (a, b) ≤ ∑ b, p (a, b) :=
      Finset.single_le_sum (fun b _ ↦ p.nonnegative (a, b)) (Finset.mem_univ b)
    _ = 0 := ha

/-- Conditional rows use the second marginal on events of probability zero. -/
@[capacity_shared_api]
noncomputable def conditionalRows [DecidableEq A] [DecidableEq B]
    (p : FiniteDistribution (A × B)) (a : A) : FiniteDistribution B := by
  classical
  exact if ha : p.map Prod.fst a = 0 then p.map Prod.snd else
    { probability := fun b ↦ p (a, b) / p.map Prod.fst a
      nonnegative := fun b ↦ div_nonneg (p.nonnegative _) ((p.map Prod.fst).nonnegative a)
      sum_probability := by rw [← Finset.sum_div, ← map_fst_apply, div_self ha] }

@[capacity_shared_api]
theorem marginal_mul_conditionalRows [DecidableEq A] [DecidableEq B]
    (p : FiniteDistribution (A × B)) (a : A) (b : B) :
    p.map Prod.fst a * p.conditionalRows a b = p (a, b) := by
  classical
  by_cases ha : p.map Prod.fst a = 0
  · simp only [ha, zero_mul, p.apply_eq_zero_of_map_fst_eq_zero ha b]
  · simp only [conditionalRows, ha, ↓reduceDIte]
    change p.map Prod.fst a * (p (a, b) / p.map Prod.fst a) = p (a, b)
    exact mul_div_cancel₀ _ ha

@[capacity_shared_api]
theorem joint_conditionalRows [DecidableEq A] [DecidableEq B]
    (p : FiniteDistribution (A × B)) :
    (p.map Prod.fst).joint p.conditionalRows = p := by
  ext z
  exact p.marginal_mul_conditionalRows z.1 z.2

end CapacityAtlas.FiniteDistribution

namespace CapacityAtlas.FiniteInformation

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

/-- Conditional information is the average information of its conditional joint laws. -/
@[capacity_shared_api]
theorem conditional_joint (p : FiniteDistribution A)
    (rows : A → FiniteDistribution (B × C)) :
    conditional (p.joint rows) (fun z ↦ z.2.1) (fun z ↦ z.2.2) Prod.fst =
      ∑ a, p a * information (rows a) Prod.fst Prod.snd := by
  classical
  have hb : entropy (p.joint rows) (fun z ↦ (z.2.1, z.1)) =
      (p.joint (fun a ↦ (rows a).map Prod.fst)).entropyBits := by
    rw [entropy_pair_swap]
    simp only [entropy_eq_map, FiniteDistribution.map_joint_snd]
  have hc : entropy (p.joint rows) (fun z ↦ (z.2.2, z.1)) =
      (p.joint (fun a ↦ (rows a).map Prod.snd)).entropyBits := by
    rw [entropy_pair_swap]
    simp only [entropy_eq_map, FiniteDistribution.map_joint_snd]
  have hbc : entropy (p.joint rows) (fun z ↦ (z.2.1, z.2.2, z.1)) =
      (p.joint rows).entropyBits := by
    rw [entropy_eq_map]
    unfold FiniteDistribution.entropyBits
    rw [FiniteDistribution.entropy_map_of_injective _ _ (by
      intro z z' hab
      rcases z with ⟨a, b, c⟩
      rcases z' with ⟨a', b', c'⟩
      simpa only [Prod.mk.injEq, and_comm, and_left_comm, and_assoc] using hab)]
  have hrow (a : A) : entropy (rows a) (fun z ↦ (z.1, z.2)) = (rows a).entropyBits := by
    rw [entropy_eq_map]
    unfold FiniteDistribution.entropyBits
    rw [FiniteDistribution.entropy_map_of_injective _ _ (by exact fun _ _ h ↦ h)]
  unfold conditional
  rw [hb, hc, hbc]
  simp only [information, hrow]
  simp only [entropy_eq_map, FiniteDistribution.map_fst_joint,
    FiniteDistribution.entropyBits, FiniteDistribution.entropy_joint]
  simp only [div_eq_mul_inv, mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← mul_assoc, ← Finset.sum_mul]
  ring

end CapacityAtlas.FiniteInformation
