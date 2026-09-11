/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.DecoderSideInformation
import CapacityAtlasForMathlib.InformationTheory.RandomCoding

open scoped BigOperators

namespace CapacityAtlas.FiniteChannel

variable {X S Y : Type*} [Fintype X] [Fintype S] [Fintype Y]

/-- A supported decoder state cancels from the likelihood ratio. -/
@[capacity_shared_api]
theorem withDecoderState_informationDensity (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) (input : FiniteDistribution X)
    (x : X) (s : S) (y : Y) (hs : state s ≠ 0) :
    (withDecoderState state channels).informationDensity input (x, (s, y)) =
      (channels s).informationDensity input (x, y) := by
  unfold informationDensity
  rw [withDecoderState_transition, withDecoderState_outputDistribution_apply,
    mul_div_mul_left _ _ hs]

/-- Decoder-state lower tails average the slice tails, including zero-probability states. -/
@[capacity_shared_api]
theorem withDecoderState_informationDensityLowerTailMass (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) (input : FiniteDistribution X) (threshold : ℝ) :
    (withDecoderState state channels).informationDensityLowerTailMass input threshold =
      ∑ s, state s * (channels s).informationDensityLowerTailMass input threshold := by
  classical
  unfold informationDensityLowerTailMass
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : state s = 0
  · simp [jointMass, withDecoderState_transition, hs]
  · simp_rw [withDecoderState_informationDensity state channels input _ s _ hs,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp [jointMass, withDecoderState_transition, mul_left_comm]

section Equivalence

variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

/-- A bijective change of input and output labels preserves every likelihood ratio. -/
@[capacity_shared_api]
theorem informationDensity_eq_of_equiv (channel : FiniteChannel A B)
    (other : FiniteChannel C D) (input : FiniteDistribution A)
    (otherInput : FiniteDistribution C) (inputEquiv : A ≃ C) (outputEquiv : B ≃ D)
    (hchannel : ∀ a b, other.transition (inputEquiv a) (outputEquiv b) =
      channel.transition a b)
    (hinput : ∀ a, otherInput (inputEquiv a) = input a) (a : A) (b : B) :
    other.informationDensity otherInput (inputEquiv a, outputEquiv b) =
      channel.informationDensity input (a, b) := by
  have houtput : other.outputDistribution otherInput (outputEquiv b) =
      channel.outputDistribution input b := by
    simp only [outputDistribution_apply]
    rw [← inputEquiv.sum_comp]
    simp_rw [hinput, hchannel]
  simp only [informationDensity, hchannel, houtput]

/-- Lower-tail mass is invariant under bijective changes preserving the channel and input law. -/
@[capacity_shared_api]
theorem informationDensityLowerTailMass_eq_of_equiv (channel : FiniteChannel A B)
    (other : FiniteChannel C D) (input : FiniteDistribution A)
    (otherInput : FiniteDistribution C) (inputEquiv : A ≃ C) (outputEquiv : B ≃ D)
    (hchannel : ∀ a b, other.transition (inputEquiv a) (outputEquiv b) =
      channel.transition a b)
    (hinput : ∀ a, otherInput (inputEquiv a) = input a) (threshold : ℝ) :
    other.informationDensityLowerTailMass otherInput threshold =
      channel.informationDensityLowerTailMass input threshold := by
  classical
  unfold informationDensityLowerTailMass
  rw [← outputEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro b _
  rw [← inputEquiv.sum_comp]
  simp_rw [informationDensity_eq_of_equiv channel other input otherInput inputEquiv
    outputEquiv hchannel hinput, jointMass, hinput, hchannel]

end Equivalence

end CapacityAtlas.FiniteChannel
