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

/-- Construct a channel from one finite distribution for each input. -/
@[capacity_shared_api]
def ofRows (rows : X → FiniteDistribution Y) : FiniteChannel X Y where
  transition input := rows input
  nonnegative input := (rows input).nonnegative
  row_sum input := (rows input).sum_probability

@[simp, capacity_shared_api]
theorem ofRows_transition (rows : X → FiniteDistribution Y) (input : X) (output : Y) :
    (ofRows rows).transition input output = rows input output :=
  rfl

@[simp, capacity_shared_api]
theorem rowDistribution_ofRows (rows : X → FiniteDistribution Y) :
    (ofRows rows).rowDistribution = rows := by
  funext input
  rfl

@[simp, capacity_shared_api]
theorem ofRows_rowDistribution (channel : FiniteChannel X Y) :
    ofRows channel.rowDistribution = channel := by
  rfl

/-- Finite channels are equivalent to functions assigning a distribution to each input. -/
@[capacity_shared_api]
def equivRows : FiniteChannel X Y ≃ (X → FiniteDistribution Y) where
  toFun := rowDistribution
  invFun := ofRows
  left_inv := ofRows_rowDistribution
  right_inv := rowDistribution_ofRows

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
  exact IsGreatest.csSup_eq ⟨⟨witness, attained⟩, by
    rintro value ⟨input, rfl⟩
    exact upper input⟩

/-- A strict lower bound on information capacity is exceeded by some input distribution. -/
@[capacity_shared_api]
theorem exists_input_of_lt_informationCapacityBits [Nonempty X]
    (channel : FiniteChannel X Y) {rate : ℝ}
    (hrate : rate < channel.informationCapacityBits) :
    ∃ input : FiniteDistribution X, rate < channel.mutualInformationBits input := by
  obtain ⟨_, ⟨input, rfl⟩, hinput⟩ := exists_lt_of_lt_csSup
    ⟨_, Set.mem_range_self (FiniteDistribution.uniform X)⟩ hrate
  exact ⟨input, hinput⟩

/-- An empty input alphabet has no information values, hence zero information capacity. -/
@[capacity_shared_api]
theorem informationCapacityBits_eq_zero_of_isEmpty [IsEmpty X]
    (channel : FiniteChannel X Y) : channel.informationCapacityBits = 0 := by
  have hvalues : Set.range channel.mutualInformationBits = ∅ := by
    ext value
    constructor
    · rintro ⟨input, rfl⟩
      have hsum := input.sum_probability
      simp at hsum
    · simp
  unfold informationCapacityBits
  rw [hvalues, Real.sSup_empty]

end FiniteChannel

end CapacityAtlas
