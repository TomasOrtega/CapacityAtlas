/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.Superposition

open scoped BigOperators

namespace CapacityAtlas.FiniteChannel

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem block_outputDistribution_productFamily (W : FiniteChannel X Y) (n : ℕ)
    (p : Fin n → FiniteDistribution X) (y : Fin n → Y) :
    (W.block n).outputDistribution (FiniteDistribution.productFamily p) y =
      ∏ i, W.outputDistribution (p i) (y i) := by
  change (∑ x : Fin n → X, (∏ i, p i (x i)) * ∏ i, W.transition (x i) (y i)) = _
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x ↦ p i x * W.transition x (y i))).symm

theorem block_informationDensity_productFamily (W : FiniteChannel X Y) (n : ℕ)
    (p : Fin n → FiniteDistribution X) (x : Fin n → X) (y : Fin n → Y)
    (hmass : (W.block n).jointMass (FiniteDistribution.productFamily p) (x, y) ≠ 0) :
    (W.block n).informationDensity (FiniteDistribution.productFamily p) (x, y) =
      ∑ i, W.informationDensity (p i) (x i, y i) := by
  have hproduct : (∏ i, p i (x i)) * (∏ i, W.transition (x i) (y i)) ≠ 0 := hmass
  have hinput (i : Fin n) : 0 < p i (x i) :=
    lt_of_le_of_ne ((p i).nonnegative _) (Ne.symm
      (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hproduct).1 i (Finset.mem_univ i)))
  have htransition (i : Fin n) : 0 < W.transition (x i) (y i) :=
    lt_of_le_of_ne (W.nonnegative _ _) (Ne.symm
      (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hproduct).2 i (Finset.mem_univ i)))
  have houtput (i : Fin n) : 0 < W.outputDistribution (p i) (y i) := by
    apply (mul_pos (hinput i) (htransition i)).trans_le
    exact Finset.single_le_sum
      (fun a _ ↦ mul_nonneg ((p i).nonnegative a) (W.nonnegative a (y i)))
      (Finset.mem_univ (x i))
  unfold informationDensity
  rw [block_transition, block_outputDistribution_productFamily, ← Finset.prod_div_distrib,
    Real.log_prod (fun i _ ↦ div_ne_zero (htransition i).ne' (houtput i).ne')]

theorem block_mutualInformationBits_productFamily_le [DecidableEq X]
    (W : FiniteChannel X Y) (n : ℕ) (p : Fin n → FiniteDistribution X) :
    (W.block n).mutualInformationBits (FiniteDistribution.productFamily p) ≤
      ∑ i, W.mutualInformationBits (p i) := by
  have h := W.block_mutualInformation_le_sum_coordinate n (FiniteDistribution.productFamily p)
  simp only [FiniteDistribution.coordinateMarginal,
    FiniteDistribution.map_productFamily_eval] at h
  unfold mutualInformationBits
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right h (Real.log_nonneg (by norm_num))

end CapacityAtlas.FiniteChannel

namespace CapacityAtlas.ConfidentialBroadcast

variable {U V Y : Type*} [Fintype U] [Fintype V] [Fintype Y]

def conditionalJoint (W : FiniteChannel V Y) (p : FiniteDistribution U)
    (q : U → FiniteDistribution V) : FiniteDistribution (U × (V × Y)) :=
  p.joint fun u ↦ (q u).joint W.rowDistribution

noncomputable def conditionalMean (W : FiniteChannel V Y) (p : FiniteDistribution U)
    (q : U → FiniteDistribution V) : ℝ :=
  ∑ u, p u * W.mutualInformation (q u)

noncomputable def conditionalDensity (W : FiniteChannel V Y)
    (q : U → FiniteDistribution V) (a : U × (V × Y)) : ℝ :=
  W.informationDensity (q a.1) a.2

noncomputable def conditionalVariance (W : FiniteChannel V Y) (p : FiniteDistribution U)
    (q : U → FiniteDistribution V) : ℝ :=
  ∑ a, conditionalJoint W p q a *
    (conditionalDensity W q a - conditionalMean W p q) ^ 2

theorem conditionalVariance_nonnegative (W : FiniteChannel V Y) (p : FiniteDistribution U)
    (q : U → FiniteDistribution V) : 0 ≤ conditionalVariance W p q := by
  exact Finset.sum_nonneg fun a _ ↦
    mul_nonneg ((conditionalJoint W p q).nonnegative a) (sq_nonneg _)

theorem expected_conditionalDensity (W : FiniteChannel V Y) (p : FiniteDistribution U)
    (q : U → FiniteDistribution V) :
    (∑ a, conditionalJoint W p q a * conditionalDensity W q a) =
      conditionalMean W p q := by
  simp only [conditionalJoint, conditionalDensity, FiniteDistribution.joint_apply,
    Fintype.sum_prod_type, mul_assoc, ← Finset.mul_sum]
  unfold conditionalMean
  apply Fintype.sum_congr
  intro u
  congr 1
  have h := W.sum_jointMass_mul_informationDensity (q u)
  simpa only [Fintype.sum_prod_type, FiniteChannel.jointMass,
    FiniteChannel.rowDistribution_apply, mul_assoc,
    ← Finset.mul_sum] using h

theorem centered_conditionalDensity_mean (W : FiniteChannel V Y) (p : FiniteDistribution U)
    (q : U → FiniteDistribution V) :
    FiniteProductProbability.mean (conditionalJoint W p q)
      (fun a ↦ conditionalDensity W q a - conditionalMean W p q) = 0 := by
  unfold FiniteProductProbability.mean
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, expected_conditionalDensity, ← Finset.sum_mul,
    FiniteDistribution.sum_probability_eq_one]
  ring

/-- The conditional information statistic satisfies the same finite-variance tail bound. -/
theorem conditionalDensity_lowerTail_le (W : FiniteChannel V Y)
    (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    (∑ a : Fin n → U × (V × Y),
      if (∑ i, conditionalDensity W q (a i)) ≤
          (n : ℝ) * conditionalMean W p q - (n : ℝ) * δ
        then (conditionalJoint W p q).iid n a else 0) ≤
      ((n : ℝ) * conditionalVariance W p q) / (((n : ℝ) * δ) ^ 2) := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmoment := FiniteProductProbability.sum_mass_mul_centered_sum_sq
    (ι := Fin n) (conditionalJoint W p q)
    (fun _ a ↦ conditionalDensity W q a - conditionalMean W p q)
    (conditionalJoint W p q).sum_probability
    (fun _ ↦ centered_conditionalDensity_mean W p q)
  have hcenter (a : Fin n → U × (V × Y)) :
      (∑ i, (conditionalDensity W q (a i) - conditionalMean W p q)) =
      (∑ i, conditionalDensity W q (a i)) - (n : ℝ) * conditionalMean W p q := by simp
  simp_rw [hcenter] at hmoment
  have htail := FiniteProductProbability.lowerTail_mass_le_secondMoment_div_sq
    (fun a : Fin n → U × (V × Y) ↦ (conditionalJoint W p q).iid n a)
    (fun a ↦ ∑ i, conditionalDensity W q (a i))
    (fun a ↦ ((conditionalJoint W p q).iid n).nonnegative a)
    ((n : ℝ) * conditionalMean W p q) ((n : ℝ) * δ) (mul_pos hnReal hδ)
  have hmoment' :
      (∑ a : Fin n → U × (V × Y), (conditionalJoint W p q).iid n a *
        ((∑ i, conditionalDensity W q (a i)) - (n : ℝ) * conditionalMean W p q) ^ 2) =
      (n : ℝ) * conditionalVariance W p q := by
    simpa [FiniteDistribution.iid_apply, FiniteProductProbability.mean,
      FiniteProductProbability.mass, conditionalVariance] using hmoment
  rw [hmoment'] at htail
  exact htail

def conditionalWordEquiv (n : ℕ) :
    ((Fin n → U) × ((Fin n → V) × (Fin n → Y))) ≃ (Fin n → U × (V × Y)) :=
  (Equiv.prodCongr (Equiv.refl (Fin n → U))
    (FiniteChannel.wordPairEquiv (X := V) (Y := Y) n)).trans
    (FiniteChannel.wordPairEquiv (X := U) (Y := V × Y) n)

theorem conditionalJoint_iid_apply (W : FiniteChannel V Y) (p : FiniteDistribution U)
    (q : U → FiniteDistribution V) (n : ℕ)
    (a : (Fin n → U) × ((Fin n → V) × (Fin n → Y))) :
    (conditionalJoint W p q).iid n (conditionalWordEquiv n a) =
      p.iid n a.1 * (W.block n).jointMass
        (FiniteDistribution.productFamily (fun i ↦ q (a.1 i))) a.2 := by
  change (∏ i, p (a.1 i) * (q (a.1 i) (a.2.1 i) * W.transition (a.2.1 i) (a.2.2 i))) =
    (∏ i, p (a.1 i)) * ((∏ i, q (a.1 i) (a.2.1 i)) *
      (∏ i, W.transition (a.2.1 i) (a.2.2 i)))
  simp only [Finset.prod_mul_distrib]

theorem conditionalLowerTail_eq (W : FiniteChannel V Y) (p : FiniteDistribution U)
    (q : U → FiniteDistribution V) (n : ℕ) (threshold : ℝ) :
    (∑ u : Fin n → U, p.iid n u *
      (W.block n).informationDensityLowerTailMass
        (FiniteDistribution.productFamily (fun i ↦ q (u i))) threshold) =
    ∑ a : Fin n → U × (V × Y),
      if (∑ i, conditionalDensity W q (a i)) ≤ threshold
        then (conditionalJoint W p q).iid n a else 0 := by
  classical
  calc
    _ = ∑ a : (Fin n → U) × ((Fin n → V) × (Fin n → Y)),
        if (W.block n).informationDensity
            (FiniteDistribution.productFamily (fun i ↦ q (a.1 i))) a.2 ≤ threshold
          then p.iid n a.1 * (W.block n).jointMass
            (FiniteDistribution.productFamily (fun i ↦ q (a.1 i))) a.2 else 0 := by
      simp only [Fintype.sum_prod_type, FiniteChannel.informationDensityLowerTailMass,
        Finset.mul_sum, mul_ite, mul_zero]
      apply Fintype.sum_congr
      intro u
      rw [Finset.sum_comm]
    _ = _ := by
      apply Fintype.sum_equiv (conditionalWordEquiv n)
      intro a
      rw [conditionalJoint_iid_apply]
      by_cases hmass : (W.block n).jointMass
          (FiniteDistribution.productFamily (fun i ↦ q (a.1 i))) a.2 = 0
      · simp [hmass]
      · rw [W.block_informationDensity_productFamily n
          (fun i ↦ q (a.1 i)) a.2.1 a.2.2 hmass]
        rfl

/-- Conditional product codebooks have a vanishing miss probability at every strict rate. -/
theorem conditionalLowerTail_le (W : FiniteChannel V Y) (p : FiniteDistribution U)
    (q : U → FiniteDistribution V) {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    (∑ u : Fin n → U, p.iid n u *
      (W.block n).informationDensityLowerTailMass
        (FiniteDistribution.productFamily (fun i ↦ q (u i)))
        ((n : ℝ) * conditionalMean W p q - (n : ℝ) * δ)) ≤
      ((n : ℝ) * conditionalVariance W p q) / (((n : ℝ) * δ) ^ 2) := by
  rw [conditionalLowerTail_eq]
  exact conditionalDensity_lowerTail_le W p q hn hδ

end CapacityAtlas.ConfidentialBroadcast
