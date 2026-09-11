/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteMixture
import CapacityAtlasForMathlib.InformationTheory.RandomCoding

open scoped BigOperators

namespace CapacityAtlas

private theorem ite_sum_zero {I : Type*} [Fintype I]
    (p : Prop) [Decidable p] (f : I → ℝ) :
    (if p then ∑ i, f i else 0) = ∑ i, if p then f i else 0 := by
  split_ifs <;> simp_all

private theorem sum_rotate {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (f : I → J → K → ℝ) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ i, ∑ j, f i j k := by
  calc
    _ = ∑ i, ∑ k, ∑ j, f i j k := by
      apply Fintype.sum_congr
      intro i
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

namespace FiniteChannel

variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

/-- A probability-weighted mixture of channels with common alphabets. -/
@[capacity_shared_api]
noncomputable def mixture (weights : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) : FiniteChannel X Y where
  transition x y := ∑ s, weights s * (channels s).transition x y
  nonnegative x y := Finset.sum_nonneg fun s _ ↦
    mul_nonneg (weights.nonnegative s) ((channels s).nonnegative x y)
  row_sum x := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_transition, mul_one]
    exact weights.sum_probability

@[simp, capacity_shared_api]
theorem mixture_transition (weights : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) (x : X) (y : Y) :
    (mixture weights channels).transition x y =
      ∑ s, weights s * (channels s).transition x y := rfl

@[capacity_shared_api]
theorem weighted_transition_le_mixture (weights : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) (s : S) (x : X) (y : Y) :
    weights s * (channels s).transition x y ≤
      (mixture weights channels).transition x y :=
  Finset.single_le_sum
    (fun t _ ↦ mul_nonneg (weights.nonnegative t) ((channels t).nonnegative x y))
    (Finset.mem_univ s)

@[capacity_shared_api]
theorem mixture_outputDistribution (weights : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) (input : FiniteDistribution X) :
    (mixture weights channels).outputDistribution input =
      FiniteDistribution.mixture weights (fun s ↦ (channels s).outputDistribution input) := by
  ext y
  change (∑ x, input x * (mixture weights channels).transition x y) =
    ∑ s, weights s * ∑ x, input x * (channels s).transition x y
  simp only [mixture_transition, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro s
  apply Fintype.sum_congr
  intro x
  ring

@[capacity_shared_api]
theorem mixture_jointMass (weights : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) (input : FiniteDistribution X) (pair : X × Y) :
    (mixture weights channels).jointMass input pair =
      ∑ s, weights s * (channels s).jointMass input pair := by
  simp only [jointMass, mixture_transition, Finset.mul_sum]
  apply Fintype.sum_congr
  intro s
  ring

private theorem informationDensity_le_of_transition_domination
    (channel reference : FiniteChannel X Y) (input : FiniteDistribution X)
    {weight γ : ℝ} (hweight : 0 < weight)
    (hdomination : ∀ x y, weight * channel.transition x y ≤ reference.transition x y)
    (x : X) (y : Y) (hmass : channel.jointMass input (x, y) ≠ 0)
    (houtput : reference.outputDistribution input y ≤
      Real.exp γ * channel.outputDistribution input y) :
    channel.informationDensity input (x, y) + Real.log weight - γ ≤
      reference.informationDensity input (x, y) := by
  have hproduct : input x * channel.transition x y ≠ 0 := hmass
  have hinputPos : 0 < input x :=
    lt_of_le_of_ne (input.nonnegative x) (Ne.symm (mul_ne_zero_iff.mp hproduct).1)
  have hchannelPos : 0 < channel.transition x y :=
    lt_of_le_of_ne (channel.nonnegative x y) (Ne.symm (mul_ne_zero_iff.mp hproduct).2)
  have hreferencePos : 0 < reference.transition x y :=
    (mul_pos hweight hchannelPos).trans_le (hdomination x y)
  have hchannelOutput : 0 < channel.outputDistribution input y := by
    apply (mul_pos hinputPos hchannelPos).trans_le
    exact Finset.single_le_sum
      (fun x' _ ↦ mul_nonneg (input.nonnegative x') (channel.nonnegative x' y))
      (Finset.mem_univ x)
  have hreferenceOutput : 0 < reference.outputDistribution input y := by
    apply (mul_pos hinputPos hreferencePos).trans_le
    exact Finset.single_le_sum
      (fun x' _ ↦ mul_nonneg (input.nonnegative x') (reference.nonnegative x' y))
      (Finset.mem_univ x)
  have htransitionLog := Real.log_le_log (mul_pos hweight hchannelPos) (hdomination x y)
  rw [Real.log_mul hweight.ne' hchannelPos.ne'] at htransitionLog
  have houtputLog := Real.log_le_log hreferenceOutput houtput
  rw [Real.log_mul (Real.exp_pos γ).ne' hchannelOutput.ne', Real.log_exp] at houtputLog
  simp only [informationDensity, Real.log_div hchannelPos.ne' hchannelOutput.ne',
    Real.log_div hreferencePos.ne' hreferenceOutput.ne']
  linarith

/-- A reference likelihood test under a dominated channel loses a logarithmic threshold
and an exponentially small output-mass term. -/
@[capacity_shared_api]
theorem informationDensityLowerTailMass_le_of_transition_domination
    (channel reference : FiniteChannel X Y) (input : FiniteDistribution X)
    (threshold γ : ℝ) {weight : ℝ} (hweight : 0 < weight)
    (hdomination : ∀ x y, weight * channel.transition x y ≤ reference.transition x y) :
    (∑ y, ∑ x,
      if reference.informationDensity input (x, y) ≤ threshold then
        channel.jointMass input (x, y) else 0) ≤
      channel.informationDensityLowerTailMass input (threshold - Real.log weight + γ) +
        Real.exp (-γ) := by
  classical
  let bad : Y → Prop := fun y ↦
    Real.exp γ * channel.outputDistribution input y < reference.outputDistribution input y
  have hpoint (x : X) (y : Y) :
      (if reference.informationDensity input (x, y) ≤ threshold then
        channel.jointMass input (x, y) else 0) ≤
      (if channel.informationDensity input (x, y) ≤ threshold - Real.log weight + γ then
        channel.jointMass input (x, y) else 0) +
      (if bad y then channel.jointMass input (x, y) else 0) := by
    by_cases hmass : channel.jointMass input (x, y) = 0
    · simp [hmass]
    have hnonnegative := channel.jointMass_nonnegative input (x, y)
    by_cases hbad : bad y
    · simp only [hbad, if_true]
      split_ifs <;> linarith
    have hgood : reference.outputDistribution input y ≤
        Real.exp γ * channel.outputDistribution input y := le_of_not_gt hbad
    have hdensity := informationDensity_le_of_transition_domination
      channel reference input hweight hdomination x y hmass hgood
    simp only [hbad, if_false, add_zero]
    split_ifs <;> linarith
  have hbadOutput (y : Y) :
      (if bad y then channel.outputDistribution input y else 0) ≤
        Real.exp (-γ) * reference.outputDistribution input y := by
    split_ifs with hbad
    · calc
        channel.outputDistribution input y =
            Real.exp (-γ) * (Real.exp γ * channel.outputDistribution input y) := by
          rw [← mul_assoc, ← Real.exp_add]
          simp
        _ ≤ Real.exp (-γ) * reference.outputDistribution input y :=
          mul_le_mul_of_nonneg_left hbad.le (Real.exp_pos _).le
    · exact mul_nonneg (Real.exp_pos _).le ((reference.outputDistribution input).nonnegative y)
  have hbadMass :
      (∑ y, ∑ x, if bad y then channel.jointMass input (x, y) else 0) ≤
        Real.exp (-γ) := by
    calc
      (∑ y, ∑ x, if bad y then channel.jointMass input (x, y) else 0) =
          ∑ y, if bad y then channel.outputDistribution input y else 0 := by
        apply Fintype.sum_congr
        intro y
        by_cases hy : bad y
        · simp only [hy, if_true]
          rfl
        · simp [hy]
      _ ≤ ∑ y, Real.exp (-γ) * reference.outputDistribution input y :=
        Finset.sum_le_sum fun y _ ↦ hbadOutput y
      _ = Real.exp (-γ) := by rw [← Finset.mul_sum, FiniteDistribution.sum_probability_eq_one, mul_one]
  calc
    _ ≤ ∑ y, ∑ x,
        ((if channel.informationDensity input (x, y) ≤ threshold - Real.log weight + γ then
          channel.jointMass input (x, y) else 0) +
        (if bad y then channel.jointMass input (x, y) else 0)) := by
      exact Finset.sum_le_sum fun y _ ↦ Finset.sum_le_sum fun x _ ↦ hpoint x y
    _ = channel.informationDensityLowerTailMass input (threshold - Real.log weight + γ) +
        ∑ y, ∑ x, if bad y then channel.jointMass input (x, y) else 0 := by
      simp only [Finset.sum_add_distrib, informationDensityLowerTailMass]
    _ ≤ _ := add_le_add_right hbadMass _

@[capacity_shared_api]
theorem informationDensityLowerTailMass_mono
    (channel : FiniteChannel X Y) (input : FiniteDistribution X)
    {lower upper : ℝ} (h : lower ≤ upper) :
    channel.informationDensityLowerTailMass input lower ≤
      channel.informationDensityLowerTailMass input upper := by
  classical
  apply Finset.sum_le_sum
  intro y _
  apply Finset.sum_le_sum
  intro x _
  have hnonnegative := channel.jointMass_nonnegative input (x, y)
  split_ifs <;> linarith

/-- The mixture lower tail is controlled by the component lower tails. Zero-weight
components contribute zero, including when their logarithm is totalized. -/
@[capacity_shared_api]
theorem mixture_informationDensityLowerTailMass_le
    (weights : FiniteDistribution S) (channels : S → FiniteChannel X Y)
    (input : FiniteDistribution X) (threshold γ : ℝ) :
    (mixture weights channels).informationDensityLowerTailMass input threshold ≤
      (∑ s, weights s * (channels s).informationDensityLowerTailMass input
        (threshold - Real.log (weights s) + γ)) + Real.exp (-γ) := by
  classical
  let reference := mixture weights channels
  let componentMass : S → ℝ := fun s ↦ ∑ y, ∑ x,
    if reference.informationDensity input (x, y) ≤ threshold then
      (channels s).jointMass input (x, y) else 0
  have hcomponent (s : S) : weights s * componentMass s ≤
      weights s * ((channels s).informationDensityLowerTailMass input
        (threshold - Real.log (weights s) + γ) + Real.exp (-γ)) := by
    by_cases hzero : weights s = 0
    · simp [hzero]
    have hpositive : 0 < weights s :=
      lt_of_le_of_ne (weights.nonnegative s) (Ne.symm hzero)
    exact mul_le_mul_of_nonneg_left
      (informationDensityLowerTailMass_le_of_transition_domination
        (channels s) reference input threshold γ hpositive
        (weighted_transition_le_mixture weights channels s)) (weights.nonnegative s)
  calc
    reference.informationDensityLowerTailMass input threshold =
        ∑ s, weights s * componentMass s := by
      simp only [informationDensityLowerTailMass, componentMass, reference,
        mixture_jointMass, Finset.mul_sum, mul_ite, mul_zero, ite_sum_zero]
      exact sum_rotate _
    _ ≤ ∑ s, weights s * ((channels s).informationDensityLowerTailMass input
        (threshold - Real.log (weights s) + γ) + Real.exp (-γ)) :=
      Finset.sum_le_sum fun s _ ↦ hcomponent s
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
        FiniteDistribution.sum_probability_eq_one, one_mul]

@[capacity_shared_api]
theorem uniformMixture_informationDensityLowerTailMass_le [Nonempty S]
    (channels : S → FiniteChannel X Y) (input : FiniteDistribution X)
    (threshold γ : ℝ) :
    (mixture (FiniteDistribution.uniform S) channels).informationDensityLowerTailMass
        input threshold ≤
      (Fintype.card S : ℝ)⁻¹ * ∑ s, (channels s).informationDensityLowerTailMass
        input (threshold + Real.log (Fintype.card S) + γ) + Real.exp (-γ) := by
  simpa only [FiniteDistribution.uniform_apply, Real.log_inv, sub_neg_eq_add,
    ← Finset.mul_sum] using
    mixture_informationDensityLowerTailMass_le (FiniteDistribution.uniform S)
      channels input threshold γ

end FiniteChannel

namespace OneShotCode

variable {S X Y M : Type*} [Fintype S] [Fintype X] [Fintype Y] [Fintype M]
variable {channel : FiniteChannel X Y}

/-- Evaluate the same encoder and decoder on another channel. -/
@[capacity_shared_api]
def onChannel (code : OneShotCode channel M) (reference : FiniteChannel X Y) :
    OneShotCode reference M where
  encode := code.encode
  decode := code.decode

@[simp, capacity_shared_api]
theorem onChannel_encode (code : OneShotCode channel M) (reference : FiniteChannel X Y) :
    (code.onChannel reference).encode = code.encode := rfl

@[simp, capacity_shared_api]
theorem onChannel_decode (code : OneShotCode channel M) (reference : FiniteChannel X Y) :
    (code.onChannel reference).decode = code.decode := rfl

@[simp, capacity_shared_api]
theorem onChannel_self (code : OneShotCode channel M) : code.onChannel channel = code := rfl

@[simp, capacity_shared_api]
theorem onChannel_onChannel (code : OneShotCode channel M)
    (reference target : FiniteChannel X Y) :
    (code.onChannel reference).onChannel target = code.onChannel target := rfl

variable [DecidableEq M] [Nonempty M]

@[capacity_shared_api]
theorem averageErrorProbability_onChannel_nonnegative (code : OneShotCode channel M)
    (reference : FiniteChannel X Y) : 0 ≤ (code.onChannel reference).averageErrorProbability := by
  rw [averageErrorProbability_eq]
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro message _
  rw [errorProbability_eq_sum_decode_ne]
  exact Finset.sum_nonneg fun y _ ↦ by
    split_ifs
    · exact reference.nonnegative _ _
    · rfl

@[capacity_shared_api]
theorem averageErrorProbability_onChannel_mixture (code : OneShotCode channel M)
    (weights : FiniteDistribution S) (channels : S → FiniteChannel X Y) :
    (code.onChannel (FiniteChannel.mixture weights channels)).averageErrorProbability =
      ∑ s, weights s * (code.onChannel (channels s)).averageErrorProbability := by
  simp only [averageErrorProbability_eq, errorProbability_eq_sum_decode_ne, onChannel_encode,
    onChannel_decode, FiniteChannel.mixture_transition, Finset.mul_sum, mul_ite, mul_zero,
    ite_sum_zero]
  rw [sum_rotate]
  apply Fintype.sum_congr
  intro s
  apply Fintype.sum_congr
  intro message
  apply Fintype.sum_congr
  intro y
  split_ifs <;> ring

@[capacity_shared_api]
theorem weighted_averageErrorProbability_le_mixture (code : OneShotCode channel M)
    (weights : FiniteDistribution S) (channels : S → FiniteChannel X Y) (s : S) :
    weights s * (code.onChannel (channels s)).averageErrorProbability ≤
      (code.onChannel (FiniteChannel.mixture weights channels)).averageErrorProbability := by
  rw [averageErrorProbability_onChannel_mixture]
  exact Finset.single_le_sum
    (fun t _ ↦ mul_nonneg (weights.nonnegative t)
      (code.averageErrorProbability_onChannel_nonnegative (channels t)))
    (Finset.mem_univ s)

@[capacity_shared_api]
theorem averageErrorProbability_le_card_mul_uniformMixture [Nonempty S]
    (code : OneShotCode channel M) (channels : S → FiniteChannel X Y) (s : S) :
    (code.onChannel (channels s)).averageErrorProbability ≤
      (Fintype.card S : ℝ) *
        (code.onChannel (FiniteChannel.mixture (FiniteDistribution.uniform S) channels)).averageErrorProbability := by
  have hcard : 0 < (Fintype.card S : ℝ) := by exact_mod_cast Fintype.card_pos
  have hbound := code.weighted_averageErrorProbability_le_mixture
    (FiniteDistribution.uniform S) channels s
  rw [FiniteDistribution.uniform_apply] at hbound
  have hscaled := mul_le_mul_of_nonneg_left hbound hcard.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hcard.ne', one_mul] using hscaled

end OneShotCode

end CapacityAtlas
