/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteChannel
import CapacityAtlasForMathlib.InformationTheory.FiniteDistribution
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

open scoped BigOperators

namespace CapacityAtlas

namespace FiniteChannel

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- A channel row regarded as a finite probability distribution. -/
@[capacity_shared_api]
def rowDistribution (channel : FiniteChannel X Y) (input : X) : FiniteDistribution Y where
  probability := channel.transition input
  nonnegative := channel.nonnegative input
  sum_probability := channel.row_sum input

@[simp, capacity_shared_api]
theorem rowDistribution_apply (channel : FiniteChannel X Y) (input : X) (output : Y) :
    channel.rowDistribution input output = channel.transition input output :=
  rfl

/-- The output distribution induced by an input distribution. -/
@[capacity_shared_api]
noncomputable def outputDistribution (channel : FiniteChannel X Y)
    (input : FiniteDistribution X) : FiniteDistribution Y where
  probability output := ∑ symbol, input symbol * channel.transition symbol output
  nonnegative output := Finset.sum_nonneg fun _ _ ↦
    mul_nonneg (input.nonnegative _) (channel.nonnegative _ output)
  sum_probability := by
    calc
      ∑ output, ∑ symbol, input symbol * channel.transition symbol output =
          ∑ symbol, ∑ output, input symbol * channel.transition symbol output := by
            rw [Finset.sum_comm]
      _ = ∑ symbol, input symbol * (∑ output, channel.transition symbol output) := by
            apply Finset.sum_congr rfl
            intro symbol _
            rw [Finset.mul_sum]
      _ = ∑ symbol, input symbol := by simp
      _ = 1 := input.sum_probability

@[simp, capacity_shared_api]
theorem outputDistribution_apply (channel : FiniteChannel X Y)
    (input : FiniteDistribution X) (output : Y) :
    channel.outputDistribution input output =
      ∑ symbol, input symbol * channel.transition symbol output :=
  rfl

/-- Output entropy conditioned on the channel input, measured in nats. -/
@[capacity_shared_api]
noncomputable def conditionalOutputEntropy (channel : FiniteChannel X Y)
    (input : FiniteDistribution X) : ℝ :=
  ∑ symbol, input symbol * (channel.rowDistribution symbol).entropy

/-- Mutual information between the input and output, measured in nats. -/
@[capacity_shared_api]
noncomputable def mutualInformation (channel : FiniteChannel X Y)
    (input : FiniteDistribution X) : ℝ :=
  (channel.outputDistribution input).entropy - channel.conditionalOutputEntropy input

/-- Mutual information between the input and output, measured in bits. -/
@[capacity_shared_api]
noncomputable def mutualInformationBits (channel : FiniteChannel X Y)
    (input : FiniteDistribution X) : ℝ :=
  channel.mutualInformation input / Real.log 2

/-- Single-letter information capacity, measured in bits per channel use. -/
@[capacity_shared_api]
noncomputable def informationCapacityBits (channel : FiniteChannel X Y) : ℝ :=
  sSup (Set.range channel.mutualInformationBits)

@[capacity_shared_api]
theorem informationCapacityBits_eq_of_upper_bound_attained
    (channel : FiniteChannel X Y) (bound : ℝ) (witness : FiniteDistribution X)
    (upper : ∀ input, channel.mutualInformationBits input ≤ bound)
    (attained : channel.mutualInformationBits witness = bound) :
    channel.informationCapacityBits = bound := by
  have hbdd : BddAbove (Set.range channel.mutualInformationBits) := by
    refine ⟨bound, ?_⟩
    rintro value ⟨input, rfl⟩
    exact upper input
  apply le_antisymm
  · exact csSup_le ⟨_, Set.mem_range_self witness⟩ fun value hvalue ↦ by
      obtain ⟨input, rfl⟩ := hvalue
      exact upper input
  · rw [← attained]
    exact le_csSup hbdd (Set.mem_range_self witness)

end FiniteChannel

end CapacityAtlas
