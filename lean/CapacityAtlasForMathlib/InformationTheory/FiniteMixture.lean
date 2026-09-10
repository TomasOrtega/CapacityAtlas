/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteEntropy

open scoped BigOperators

namespace CapacityAtlas

namespace FiniteDistribution

variable {I X : Type*} [Fintype I] [Fintype X]

/-- A probability-weighted mixture of finitely many distributions. -/
@[capacity_shared_api]
noncomputable def mixture (weights : FiniteDistribution I)
    (inputs : I → FiniteDistribution X) : FiniteDistribution X where
  probability x := ∑ i, weights i * inputs i x
  nonnegative x := Finset.sum_nonneg fun i _ ↦
    mul_nonneg (weights.nonnegative i) ((inputs i).nonnegative x)
  sum_probability := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_probability_eq_one, mul_one]
    exact weights.sum_probability

@[simp, capacity_shared_api]
theorem mixture_apply (weights : FiniteDistribution I)
    (inputs : I → FiniteDistribution X) (x : X) :
    mixture weights inputs x = ∑ i, weights i * inputs i x := rfl

/-- Finite expectation is affine in the input distribution. -/
@[capacity_shared_api]
theorem sum_mixture_mul (weights : FiniteDistribution I)
    (inputs : I → FiniteDistribution X) (observable : X → ℝ) :
    ∑ x, mixture weights inputs x * observable x =
      ∑ i, weights i * ∑ x, inputs i x * observable x := by
  simp only [mixture_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- Entropy is concave under finite probability mixtures. -/
@[capacity_shared_api]
theorem entropy_mixture_ge (weights : FiniteDistribution I)
    (inputs : I → FiniteDistribution X) :
    ∑ i, weights i * (inputs i).entropy ≤ (mixture weights inputs).entropy := by
  unfold entropy
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  simpa only [smul_eq_mul, mixture_apply] using
    Real.concaveOn_negMulLog.le_map_sum
      (t := Finset.univ) (w := fun i ↦ weights i) (p := fun i ↦ inputs i x)
      (fun i _ ↦ weights.nonnegative i) weights.sum_probability
      (fun i _ ↦ (inputs i).nonnegative x)

/-- A distribution concentrated at one point. -/
@[capacity_shared_api]
def atom [DecidableEq X] (point : X) : FiniteDistribution X where
  probability x := if x = point then 1 else 0
  nonnegative _ := by split_ifs <;> norm_num
  sum_probability := by simp

@[simp, capacity_shared_api]
theorem atom_apply [DecidableEq X] (point x : X) :
    atom point x = if x = point then 1 else 0 := rfl

@[simp, capacity_shared_api]
theorem sum_atom_mul [DecidableEq X] (point : X) (observable : X → ℝ) :
    ∑ x, atom point x * observable x = observable point := by
  simp [atom_apply]

/-- The mixture assigning weights `1 - t` and `t` to its two inputs. -/
@[capacity_shared_api]
noncomputable def binaryMixture (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (left right : FiniteDistribution X) : FiniteDistribution X :=
  mixture (bernoulli t ht0 ht1) (fun choice ↦ if choice then right else left)

@[simp, capacity_shared_api]
theorem binaryMixture_apply (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (left right : FiniteDistribution X) (x : X) :
    binaryMixture t ht0 ht1 left right x = (1 - t) * left x + t * right x := by
  simp [binaryMixture, add_comm]

@[capacity_shared_api]
theorem sum_binaryMixture_mul (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (left right : FiniteDistribution X) (observable : X → ℝ) :
    ∑ x, binaryMixture t ht0 ht1 left right x * observable x =
      (1 - t) * (∑ x, left x * observable x) + t * (∑ x, right x * observable x) := by
  simp only [binaryMixture_apply, add_mul, Finset.sum_add_distrib, mul_assoc,
    ← Finset.mul_sum]

end FiniteDistribution

namespace FiniteChannel

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]

/-- Channel output commutes with a finite mixture of input laws. -/
@[capacity_shared_api]
theorem outputDistribution_mixture (channel : FiniteChannel X Y)
    (weights : FiniteDistribution I) (inputs : I → FiniteDistribution X) :
    channel.outputDistribution (FiniteDistribution.mixture weights inputs) =
      FiniteDistribution.mixture weights (fun i ↦ channel.outputDistribution (inputs i)) := by
  ext y
  exact FiniteDistribution.sum_mixture_mul weights inputs (fun x ↦ channel.transition x y)

@[capacity_shared_api]
theorem conditionalOutputEntropy_mixture (channel : FiniteChannel X Y)
    (weights : FiniteDistribution I) (inputs : I → FiniteDistribution X) :
    channel.conditionalOutputEntropy (FiniteDistribution.mixture weights inputs) =
      ∑ i, weights i * channel.conditionalOutputEntropy (inputs i) :=
  FiniteDistribution.sum_mixture_mul weights inputs (fun x ↦ (channel.rowDistribution x).entropy)

/-- Mutual information is concave in the input distribution. -/
@[capacity_shared_api]
theorem mutualInformation_mixture_ge (channel : FiniteChannel X Y)
    (weights : FiniteDistribution I) (inputs : I → FiniteDistribution X) :
    ∑ i, weights i * channel.mutualInformation (inputs i) ≤
      channel.mutualInformation (FiniteDistribution.mixture weights inputs) := by
  simp only [mutualInformation, outputDistribution_mixture, conditionalOutputEntropy_mixture,
    mul_sub, Finset.sum_sub_distrib]
  exact sub_le_sub_right
    (FiniteDistribution.entropy_mixture_ge weights (fun i ↦ channel.outputDistribution (inputs i))) _

@[capacity_shared_api]
theorem mutualInformationBits_mixture_ge (channel : FiniteChannel X Y)
    (weights : FiniteDistribution I) (inputs : I → FiniteDistribution X) :
    ∑ i, weights i * channel.mutualInformationBits (inputs i) ≤
      channel.mutualInformationBits (FiniteDistribution.mixture weights inputs) := by
  simp only [mutualInformationBits, ← mul_div_assoc, ← Finset.sum_div]
  exact div_le_div_of_nonneg_right (channel.mutualInformation_mixture_ge weights inputs)
    (Real.log_nonneg (by norm_num))

@[capacity_shared_api]
theorem mutualInformation_binaryMixture_ge (channel : FiniteChannel X Y)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (left right : FiniteDistribution X) :
    (1 - t) * channel.mutualInformation left + t * channel.mutualInformation right ≤
      channel.mutualInformation (FiniteDistribution.binaryMixture t ht0 ht1 left right) := by
  simpa [FiniteDistribution.binaryMixture, add_comm] using
    channel.mutualInformation_mixture_ge (FiniteDistribution.bernoulli t ht0 ht1)
      (fun choice ↦ if choice then right else left)

@[capacity_shared_api]
theorem mutualInformationBits_binaryMixture_ge (channel : FiniteChannel X Y)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (left right : FiniteDistribution X) :
    (1 - t) * channel.mutualInformationBits left + t * channel.mutualInformationBits right ≤
      channel.mutualInformationBits (FiniteDistribution.binaryMixture t ht0 ht1 left right) := by
  simpa [FiniteDistribution.binaryMixture, add_comm] using
    channel.mutualInformationBits_mixture_ge (FiniteDistribution.bernoulli t ht0 ht1)
      (fun choice ↦ if choice then right else left)

@[capacity_shared_api]
theorem mutualInformation_binaryMixture_atom_ge [DecidableEq X]
    (channel : FiniteChannel X Y) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (input : FiniteDistribution X) (point : X) :
    (1 - t) * channel.mutualInformation input ≤
      channel.mutualInformation
        (FiniteDistribution.binaryMixture t ht0 ht1 input (FiniteDistribution.atom point)) := by
  exact (le_add_of_nonneg_right (mul_nonneg ht0 (channel.mutualInformation_nonnegative _))).trans
    (channel.mutualInformation_binaryMixture_ge t ht0 ht1 input (FiniteDistribution.atom point))

@[capacity_shared_api]
theorem mutualInformationBits_binaryMixture_atom_ge [DecidableEq X]
    (channel : FiniteChannel X Y) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (input : FiniteDistribution X) (point : X) :
    (1 - t) * channel.mutualInformationBits input ≤
      channel.mutualInformationBits
        (FiniteDistribution.binaryMixture t ht0 ht1 input (FiniteDistribution.atom point)) := by
  have hnonneg : 0 ≤ channel.mutualInformationBits (FiniteDistribution.atom point) :=
    div_nonneg (channel.mutualInformation_nonnegative _) (Real.log_nonneg (by norm_num))
  exact (le_add_of_nonneg_right (mul_nonneg ht0 hnonneg)).trans
    (channel.mutualInformationBits_binaryMixture_ge t ht0 ht1 input (FiniteDistribution.atom point))

end FiniteChannel

end CapacityAtlas
