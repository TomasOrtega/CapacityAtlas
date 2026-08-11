/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.OperationalCapacity
import CapacityAtlasForMathlib.InformationTheory.FiniteProductProbability

open scoped BigOperators

namespace CapacityAtlas

namespace FiniteDistribution

variable {A : Type*} [Fintype A]

/-- The i.i.d. product of a finite distribution. -/
@[capacity_shared_api]
def iid (distribution : FiniteDistribution A) (n : ℕ) :
    FiniteDistribution (Fin n → A) where
  probability := FiniteProductProbability.mass distribution
  nonnegative := FiniteProductProbability.mass_nonnegative distribution distribution.nonnegative
  sum_probability :=
    FiniteProductProbability.sum_mass distribution distribution.sum_probability

@[simp, capacity_shared_api]
theorem iid_apply (distribution : FiniteDistribution A) (n : ℕ) (word : Fin n → A) :
    distribution.iid n word = ∏ i, distribution (word i) :=
  rfl

end FiniteDistribution

namespace FiniteChannel

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Joint input-output mass induced by an input distribution and a channel. -/
@[capacity_shared_api]
def jointMass (channel : FiniteChannel X Y) (input : FiniteDistribution X)
    (pair : X × Y) : ℝ :=
  input pair.1 * channel.transition pair.1 pair.2

@[capacity_shared_api]
theorem jointMass_nonnegative (channel : FiniteChannel X Y) (input : FiniteDistribution X)
    (pair : X × Y) : 0 ≤ channel.jointMass input pair :=
  mul_nonneg (input.nonnegative pair.1) (channel.nonnegative pair.1 pair.2)

@[capacity_shared_api]
theorem sum_jointMass (channel : FiniteChannel X Y) (input : FiniteDistribution X) :
    ∑ pair : X × Y, channel.jointMass input pair = 1 := by
  rw [Fintype.sum_prod_type]
  calc
    ∑ x : X, ∑ y : Y, channel.jointMass input (x, y) =
        ∑ x : X, input x * ∑ y : Y, channel.transition x y := by
      apply Fintype.sum_congr
      intro x
      rw [Finset.mul_sum]
      rfl
    _ = ∑ x : X, input x := by simp
    _ = 1 := input.sum_probability

/-- Information density `log (W(y|x) / P_Y(y))`, measured in nats. -/
@[capacity_shared_api]
noncomputable def informationDensity (channel : FiniteChannel X Y)
    (input : FiniteDistribution X) (pair : X × Y) : ℝ :=
  Real.log (channel.transition pair.1 pair.2 / channel.outputDistribution input pair.2)

/-- Information-density variance under the induced joint distribution. -/
@[capacity_shared_api]
noncomputable def informationVariance (channel : FiniteChannel X Y)
    (input : FiniteDistribution X) : ℝ :=
  ∑ pair : X × Y, channel.jointMass input pair *
    (channel.informationDensity input pair - channel.mutualInformation input) ^ 2

@[capacity_shared_api]
theorem informationVariance_nonnegative (channel : FiniteChannel X Y)
    (input : FiniteDistribution X) : 0 ≤ channel.informationVariance input := by
  unfold informationVariance
  exact Finset.sum_nonneg fun pair _ ↦
    mul_nonneg (channel.jointMass_nonnegative input pair) (sq_nonneg _)

private theorem jointMass_mul_informationDensity
    (channel : FiniteChannel X Y) (input : FiniteDistribution X) (x : X) (y : Y) :
    channel.jointMass input (x, y) * channel.informationDensity input (x, y) =
      input x * channel.transition x y * Real.log (channel.transition x y) -
        input x * channel.transition x y * Real.log (channel.outputDistribution input y) := by
  by_cases hinput : input x = 0
  · simp [jointMass, informationDensity, hinput]
  by_cases htransition : channel.transition x y = 0
  · simp [jointMass, informationDensity, htransition]
  have hinputPos : 0 < input x := lt_of_le_of_ne (input.nonnegative x) (Ne.symm hinput)
  have htransitionPos : 0 < channel.transition x y :=
    lt_of_le_of_ne (channel.nonnegative x y) (Ne.symm htransition)
  have hsummandPos : 0 < input x * channel.transition x y :=
    mul_pos hinputPos htransitionPos
  have houtputPos : 0 < channel.outputDistribution input y := by
    apply hsummandPos.trans_le
    exact Finset.single_le_sum
      (fun x' _ ↦ mul_nonneg (input.nonnegative x') (channel.nonnegative x' y))
      (Finset.mem_univ x)
  rw [jointMass, informationDensity, Real.log_div htransition houtputPos.ne']
  ring

/-- Mutual information is the expectation of information density. -/
@[capacity_shared_api]
theorem sum_jointMass_mul_informationDensity
    (channel : FiniteChannel X Y) (input : FiniteDistribution X) :
    ∑ pair : X × Y,
        channel.jointMass input pair * channel.informationDensity input pair =
      channel.mutualInformation input := by
  rw [Fintype.sum_prod_type]
  simp_rw [jointMass_mul_informationDensity channel input]
  simp_rw [Finset.sum_sub_distrib]
  have hrowTerm :
      (∑ x : X, ∑ y : Y,
        input x * channel.transition x y * Real.log (channel.transition x y)) =
        ∑ x : X, input x * ∑ y : Y,
          channel.transition x y * Real.log (channel.transition x y) := by
    apply Fintype.sum_congr
    intro x
    rw [Finset.mul_sum]
    apply Fintype.sum_congr
    intro y
    ring
  have houtputTerm :
      (∑ x : X, ∑ y : Y,
        input x * channel.transition x y * Real.log (channel.outputDistribution input y)) =
        ∑ y : Y, channel.outputDistribution input y *
          Real.log (channel.outputDistribution input y) := by
    rw [Finset.sum_comm]
    apply Fintype.sum_congr
    intro y
    rw [← Finset.sum_mul]
    rfl
  rw [hrowTerm, houtputTerm]
  unfold mutualInformation conditionalOutputEntropy FiniteDistribution.entropy
  simp only [rowDistribution_apply, Real.negMulLog_def]
  have houtputNeg :
      (∑ y : Y, -channel.outputDistribution input y *
        Real.log (channel.outputDistribution input y)) =
        -(∑ y : Y, channel.outputDistribution input y *
          Real.log (channel.outputDistribution input y)) := by
    rw [← Finset.sum_neg_distrib]
    apply Fintype.sum_congr
    intro y
    ring
  have hrowNeg :
      (∑ x : X, input x * ∑ y : Y,
        -channel.transition x y * Real.log (channel.transition x y)) =
        -(∑ x : X, input x * ∑ y : Y,
          channel.transition x y * Real.log (channel.transition x y)) := by
    rw [← Finset.sum_neg_distrib]
    apply Fintype.sum_congr
    intro x
    have hinner :
        (∑ y : Y, -channel.transition x y * Real.log (channel.transition x y)) =
          -(∑ y : Y, channel.transition x y * Real.log (channel.transition x y)) := by
      rw [← Finset.sum_neg_distrib]
      apply Fintype.sum_congr
      intro y
      ring
    rw [hinner]
    ring
  rw [houtputNeg, hrowNeg]
  ring

/-- Coordinatewise pairing identifies a pair of words with a word of pairs. -/
@[capacity_shared_api]
def wordPairEquiv (n : ℕ) :
    ((Fin n → X) × (Fin n → Y)) ≃ (Fin n → X × Y) where
  toFun words i := (words.1 i, words.2 i)
  invFun pairs := (fun i ↦ (pairs i).1, fun i ↦ (pairs i).2)
  left_inv words := by ext i <;> rfl
  right_inv pairs := by ext i <;> rfl

/-- An i.i.d. input passed through a memoryless channel has an i.i.d. output. -/
@[simp, capacity_shared_api]
theorem block_outputDistribution_iid_apply
    (channel : FiniteChannel X Y) (input : FiniteDistribution X) (n : ℕ)
    (output : Fin n → Y) :
    (channel.block n).outputDistribution (input.iid n) output =
      FiniteProductProbability.mass (channel.outputDistribution input) output := by
  unfold outputDistribution FiniteDistribution.iid FiniteProductProbability.mass block
  calc
    ∑ word : Fin n → X,
        (∏ i, input (word i)) * ∏ i, channel.transition (word i) (output i) =
        ∑ word : Fin n → X,
          ∏ i, input (word i) * channel.transition (word i) (output i) := by
      apply Fintype.sum_congr
      intro word
      rw [Finset.prod_mul_distrib]
    _ = ∏ i, ∑ symbol : X,
        input symbol * channel.transition symbol (output i) := by
      simpa only using
        (Fintype.prod_sum
          (fun i symbol ↦ input symbol * channel.transition symbol (output i))).symm
    _ = ∏ i, channel.outputDistribution input (output i) := by rfl

/-- The joint mass of a memoryless block is the product of its coordinate joint masses. -/
@[simp, capacity_shared_api]
theorem block_jointMass_iid
    (channel : FiniteChannel X Y) (input : FiniteDistribution X) (n : ℕ)
    (words : (Fin n → X) × (Fin n → Y)) :
    (channel.block n).jointMass (input.iid n) words =
      FiniteProductProbability.mass (channel.jointMass input) (wordPairEquiv n words) := by
  change
    (∏ i, input (words.1 i)) *
        (∏ i, channel.transition (words.1 i) (words.2 i)) =
      ∏ i, input (words.1 i) * channel.transition (words.1 i) (words.2 i)
  rw [Finset.prod_mul_distrib]

/-- On the support of the block joint distribution, information density is additive. -/
@[capacity_shared_api]
theorem block_informationDensity_eq_sum
    (channel : FiniteChannel X Y) (input : FiniteDistribution X) (n : ℕ)
    (words : (Fin n → X) × (Fin n → Y))
    (hmass : (channel.block n).jointMass (input.iid n) words ≠ 0) :
    (channel.block n).informationDensity (input.iid n) words =
      ∑ i, channel.informationDensity input (words.1 i, words.2 i) := by
  have hproduct :
      ((∏ i, input (words.1 i)) *
        ∏ i, channel.transition (words.1 i) (words.2 i)) ≠ 0 := by
    simpa [jointMass, FiniteDistribution.iid_apply, block_transition] using hmass
  have hinputProduct : (∏ i, input (words.1 i)) ≠ 0 :=
    (mul_ne_zero_iff.mp hproduct).1
  have htransitionProduct :
      (∏ i, channel.transition (words.1 i) (words.2 i)) ≠ 0 :=
    (mul_ne_zero_iff.mp hproduct).2
  have hinput (i : Fin n) : 0 < input (words.1 i) := by
    exact lt_of_le_of_ne (input.nonnegative _) <|
      Ne.symm (Finset.prod_ne_zero_iff.mp hinputProduct i (Finset.mem_univ i))
  have htransition (i : Fin n) : 0 < channel.transition (words.1 i) (words.2 i) := by
    exact lt_of_le_of_ne (channel.nonnegative _ _) <|
      Ne.symm (Finset.prod_ne_zero_iff.mp htransitionProduct i (Finset.mem_univ i))
  have houtput (i : Fin n) : 0 < channel.outputDistribution input (words.2 i) := by
    apply (mul_pos (hinput i) (htransition i)).trans_le
    exact Finset.single_le_sum
      (fun symbol _ ↦ mul_nonneg (input.nonnegative symbol)
        (channel.nonnegative symbol (words.2 i)))
      (Finset.mem_univ (words.1 i))
  unfold informationDensity
  rw [block_transition, block_outputDistribution_iid_apply]
  unfold FiniteProductProbability.mass
  rw [← Finset.prod_div_distrib,
    Real.log_prod (fun i _ ↦ div_ne_zero (htransition i).ne' (houtput i).ne')]

/-- The information density accumulated over independent channel uses. -/
@[capacity_shared_api]
noncomputable def blockInformationDensity (channel : FiniteChannel X Y)
    (input : FiniteDistribution X) {n : ℕ} (pairs : Fin n → X × Y) : ℝ :=
  ∑ i, channel.informationDensity input (pairs i)

/-- The centered one-coordinate information density has mean zero. -/
@[capacity_shared_api]
theorem mean_centeredInformationDensity
    (channel : FiniteChannel X Y) (input : FiniteDistribution X) :
    FiniteProductProbability.mean (channel.jointMass input)
        (fun pair ↦ channel.informationDensity input pair -
          channel.mutualInformation input) = 0 := by
  unfold FiniteProductProbability.mean
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, channel.sum_jointMass_mul_informationDensity input,
    ← Finset.sum_mul, channel.sum_jointMass input]
  ring

/-- The second centered moment of an i.i.d. information-density sum grows linearly. -/
@[capacity_shared_api]
theorem sum_productMass_mul_blockInformationDensity_sub_mean_sq
    (channel : FiniteChannel X Y) (input : FiniteDistribution X) (n : ℕ) :
    ∑ pairs : Fin n → X × Y,
        FiniteProductProbability.mass (channel.jointMass input) pairs *
          (channel.blockInformationDensity input pairs -
            (n : ℝ) * channel.mutualInformation input) ^ 2 =
      (n : ℝ) * channel.informationVariance input := by
  let centered : Fin n → X × Y → ℝ := fun _ pair ↦
    channel.informationDensity input pair - channel.mutualInformation input
  have hmoment := FiniteProductProbability.sum_mass_mul_centered_sum_sq
    (ι := Fin n) (channel.jointMass input) centered
    (channel.sum_jointMass input)
    (fun _ ↦ channel.mean_centeredInformationDensity input)
  have hcenteredSum (pairs : Fin n → X × Y) :
      (∑ i, centered i (pairs i)) =
        channel.blockInformationDensity input pairs -
          (n : ℝ) * channel.mutualInformation input := by
    unfold centered blockInformationDensity
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  calc
    ∑ pairs : Fin n → X × Y,
        FiniteProductProbability.mass (channel.jointMass input) pairs *
          (channel.blockInformationDensity input pairs -
            (n : ℝ) * channel.mutualInformation input) ^ 2 =
        ∑ pairs : Fin n → X × Y,
          FiniteProductProbability.mass (channel.jointMass input) pairs *
            (∑ i, centered i (pairs i)) ^ 2 := by
      apply Fintype.sum_congr
      intro pairs
      rw [hcenteredSum]
    _ = ∑ i, FiniteProductProbability.mean (channel.jointMass input)
          (fun pair ↦ (centered i pair) ^ 2) := hmoment
    _ = (n : ℝ) * channel.informationVariance input := by
      unfold centered informationVariance FiniteProductProbability.mean
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- A Chebyshev lower-tail estimate for i.i.d. information density. -/
@[capacity_shared_api]
theorem blockInformationDensity_lowerTail_le
    (channel : FiniteChannel X Y) (input : FiniteDistribution X)
    {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    (∑ pairs : Fin n → X × Y,
      if channel.blockInformationDensity input pairs ≤
          (n : ℝ) * channel.mutualInformation input - (n : ℝ) * δ then
        FiniteProductProbability.mass (channel.jointMass input) pairs
      else 0) ≤
      ((n : ℝ) * channel.informationVariance input) / (((n : ℝ) * δ) ^ 2) := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have htail := FiniteProductProbability.lowerTail_mass_le_secondMoment_div_sq
    (α := Fin n → X × Y)
    (FiniteProductProbability.mass (ι := Fin n) (channel.jointMass input))
    (channel.blockInformationDensity input (n := n))
    (FiniteProductProbability.mass_nonnegative (ι := Fin n) _
      (channel.jointMass_nonnegative input))
    ((n : ℝ) * channel.mutualInformation input) ((n : ℝ) * δ)
    (mul_pos hnReal hδ)
  rw [channel.sum_productMass_mul_blockInformationDensity_sub_mean_sq input n] at htail
  exact htail

end FiniteChannel

end CapacityAtlas
