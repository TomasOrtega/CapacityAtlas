/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.Converse
import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.SingleLetter
import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.Prefixing

open scoped BigOperators

namespace CapacityAtlas.ConfidentialBroadcast

open FiniteInformation

variable {U V X Y Z O : Type*} [Fintype U] [Fintype V] [Fintype X]
    [Fintype Y] [Fintype Z] [Fintype O]

private theorem information_nonnegative {Ω A B : Type*}
    [Fintype Ω] [Fintype A] [Fintype B]
    (p : FiniteDistribution Ω) (f : Ω → A) (g : Ω → B) : 0 ≤ information p f g := by
  simpa only [conditional_const] using conditional_nonneg p f g (fun _ ↦ ())

private theorem conditional_self {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]
    (p : FiniteDistribution Ω) (f : Ω → A) (g : Ω → B) : conditional p f g f = 0 := by
  have hle := conditional_le_conditionalEntropy p f g f
  have he := entropy_comp_injective p f (fun a ↦ (a, a))
    (fun _ _ h ↦ (Prod.mk.inj h).1)
  simp only [Function.comp_def] at he
  unfold conditionalEntropy at hle
  rw [he, sub_self] at hle
  exact le_antisymm hle (conditional_nonneg p f g f)

private theorem diagonal_joint [DecidableEq U] [DecidableEq O]
    (p : FiniteDistribution U) (P : FiniteChannel U X) (B : FiniteChannel X O) :
    auxiliaryJoint (p.map (fun u ↦ (u, u))) P B =
      (joint p (B.comp P)).map (fun z ↦ ((z.1, z.1), z.2)) := by
  exact (FiniteDistribution.map_joint_fst p (fun u ↦ (u, u))
    (fun z : U × U ↦ (B.comp P).rowDistribution z.2)).symm

private theorem diagonal_information [DecidableEq U]
    (p : FiniteDistribution U) (P : FiniteChannel U X) (B : FiniteChannel X O) :
    information (auxiliaryJoint (p.map (fun u ↦ (u, u))) P B)
      (fun z ↦ z.1.1) Prod.snd = (B.comp P).mutualInformationBits p := by
  classical
  rw [diagonal_joint, information_map]
  exact information_joint_fst_snd p (B.comp P)

private theorem diagonal_conditional [DecidableEq U]
    (p : FiniteDistribution U) (P : FiniteChannel U X) (B : FiniteChannel X O) :
    conditional (auxiliaryJoint (p.map (fun u ↦ (u, u))) P B)
      (fun z ↦ z.1.2) Prod.snd (fun z ↦ z.1.1) = 0 := by
  classical
  rw [diagonal_joint, conditional_map]
  exact conditional_self (joint p (B.comp P)) Prod.fst Prod.snd

private theorem diagonal_information_of_joint [DecidableEq U] [DecidableEq V]
    (p : FiniteDistribution (U × V)) (P : FiniteChannel V X) (B : FiniteChannel X O) :
    information (auxiliaryJoint ((p.map Prod.fst).map (fun u ↦ (u, u)))
      (P.comp (FiniteChannel.ofRows p.conditionalRows)) B) (fun z ↦ z.1.1) Prod.snd =
    information (auxiliaryJoint p P B) (fun z ↦ z.1.1) Prod.snd := by
  classical
  rw [diagonal_information]
  have h := auxiliary_information_eq_composed (p.map Prod.fst) p.conditionalRows P B
  rw [p.joint_conditionalRows, FiniteChannel.comp_assoc] at h
  exact h.symm

/-- Replacing the secret auxiliary by the public one removes a negative secrecy difference. -/
theorem auxiliaryRegion_clipped (W : FiniteBroadcastChannel X Y Z)
    (p : FiniteDistribution (U × V)) (P : FiniteChannel V X) :
    (min (information (auxiliaryJoint p P W.receiver₁) (fun z ↦ z.1.1) Prod.snd)
        (information (auxiliaryJoint p P W.receiver₂) (fun z ↦ z.1.1) Prod.snd),
      max 0 (conditional (auxiliaryJoint p P W.receiver₁) (fun z ↦ z.1.2) Prod.snd (fun z ↦ z.1.1) -
        conditional (auxiliaryJoint p P W.receiver₂) (fun z ↦ z.1.2) Prod.snd (fun z ↦ z.1.1))) ∈
      auxiliaryRegion W := by
  classical
  let Iy := information (auxiliaryJoint p P W.receiver₁) (fun z ↦ z.1.1) Prod.snd
  let Iz := information (auxiliaryJoint p P W.receiver₂) (fun z ↦ z.1.1) Prod.snd
  let D := conditional (auxiliaryJoint p P W.receiver₁) (fun z ↦ z.1.2) Prod.snd (fun z ↦ z.1.1) -
    conditional (auxiliaryJoint p P W.receiver₂) (fun z ↦ z.1.2) Prod.snd (fun z ↦ z.1.1)
  have hI : 0 ≤ min Iy Iz := le_min (information_nonnegative _ _ _) (information_nonnegative _ _ _)
  change (min Iy Iz, max 0 D) ∈ auxiliaryRegion W
  by_cases hD : 0 ≤ D
  · rw [max_eq_right hD]
    exact mem_auxiliaryRegion_of_finite W p P hI hD (min_le_left _ _) (min_le_right _ _) le_rfl
  · rw [max_eq_left (le_of_not_ge hD)]
    let p₀ := p.map Prod.fst
    let Q := FiniteChannel.ofRows p.conditionalRows
    let P₀ := P.comp Q
    apply mem_auxiliaryRegion_of_finite W (p₀.map (fun u ↦ (u, u))) P₀ hI le_rfl
    · rw [diagonal_information_of_joint p P W.receiver₁]
      exact min_le_left _ _
    · rw [diagonal_information_of_joint p P W.receiver₂]
      exact min_le_right _ _
    · rw [diagonal_conditional, diagonal_conditional, sub_self]

namespace Code

variable {W : FiniteBroadcastChannel X Y Z} {n : ℕ}

theorem exists_auxiliary_converse_bound (c : Code W n) (hn : 0 < n) :
    ∃ r ∈ auxiliaryRegion W,
      (1 - c.error) * c.rates.1 ≤ r.1 + (n : ℝ)⁻¹ ∧
      (1 - c.error) * c.rates.2 - c.error * c.rates.1 ≤
        r.2 + c.leakage + 2 / (n : ℝ) := by
  classical
  letI : NeZero n := ⟨hn.ne'⟩
  let Iy := information (auxiliaryJoint c.auxiliaryLaw c.prefixing W.receiver₁)
    (fun z ↦ z.1.1) Prod.snd
  let Iz := information (auxiliaryJoint c.auxiliaryLaw c.prefixing W.receiver₂)
    (fun z ↦ z.1.1) Prod.snd
  let D := conditional (auxiliaryJoint c.auxiliaryLaw c.prefixing W.receiver₁)
      (fun z ↦ z.1.2) Prod.snd (fun z ↦ z.1.1) -
    conditional (auxiliaryJoint c.auxiliaryLaw c.prefixing W.receiver₂)
      (fun z ↦ z.1.2) Prod.snd (fun z ↦ z.1.1)
  refine ⟨(min Iy Iz, max 0 D), auxiliaryRegion_clipped W c.auxiliaryLaw c.prefixing, ?_, ?_⟩
  · have hY : (1 - c.error) * c.rates.1 ≤
        information (c.joint W.receiver₁) (fun z ↦ z.1.1) Prod.snd / n + (n : ℝ)⁻¹ := by
      have h := div_le_div_of_nonneg_right c.common_fano_legitimate
        (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      simpa only [rates, Operational.messageRate, Real.logb, add_div, one_div,
        mul_div_assoc] using h
    have hY' : (1 - c.error) * c.rates.1 ≤ Iy + (n : ℝ)⁻¹ := by
      have hi : information (c.joint W.receiver₁) (fun z ↦ z.1.1) Prod.snd / n ≤ Iy :=
        c.common_information_le_auxiliary_legitimate
      linarith
    have hZ' : (1 - c.error) * c.rates.1 ≤ Iz + (n : ℝ)⁻¹ := by
      have hi : information (c.joint W.receiver₂) (fun z ↦ z.1.1) Prod.snd / n ≤ Iz :=
        c.common_information_le_auxiliary_eavesdropper
      have hf := c.common_rate_fano
      linarith
    change _ ≤ min Iy Iz + (n : ℝ)⁻¹
    rcases le_total Iy Iz with h | h
    · simpa only [min_eq_left h] using hY'
    · simpa only [min_eq_right h] using hZ'
  · have hs := c.secret_rate_information_bound
    rw [← c.secrecy_difference_eq] at hs
    change _ ≤ D + c.leakage + 2 / (n : ℝ) at hs
    change _ ≤ max 0 D + c.leakage + 2 / (n : ℝ)
    linarith [le_max_right 0 D]

end Code

/-- Every achievable common/secret rate belongs to the single-letter region. -/
theorem capacityRegion_subset_informationRegion (W : FiniteBroadcastChannel X Y Z) :
    capacityRegion W ⊆ informationRegion W :=
  capacityRegion_subset_informationRegion_of_code_bounds
    (fun _ hn c ↦ c.exists_auxiliary_converse_bound hn)

end CapacityAtlas.ConfidentialBroadcast
