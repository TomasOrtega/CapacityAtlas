/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteChannelCapacity
import CapacityAtlasForMathlib.InformationTheory.FiniteDistribution.PMF

/-! Channel rows and serial composition as probability mass functions. -/

open scoped BigOperators

namespace CapacityAtlas.FiniteChannel

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- A channel viewed as mathlib probability mass functions indexed by the input. -/
@[capacity_shared_api]
noncomputable def toPMF (channel : FiniteChannel X Y) (input : X) : PMF Y :=
  (channel.rowDistribution input).toPMF

@[simp, capacity_shared_api]
theorem toPMF_apply (channel : FiniteChannel X Y) (input : X) (output : Y) :
    channel.toPMF input output = ENNReal.ofReal (channel.transition input output) := rfl

/-- Passing a random input through a channel agrees with mathlib's sampling composition. -/
@[simp, capacity_shared_api]
theorem toPMF_outputDistribution (channel : FiniteChannel X Y)
    (input : FiniteDistribution X) :
    (channel.outputDistribution input).toPMF = input.toPMF.bind channel.toPMF := by
  ext output
  simp only [FiniteDistribution.toPMF_apply, outputDistribution_apply, PMF.bind_apply,
    tsum_fintype, toPMF_apply]
  rw [ENNReal.ofReal_sum_of_nonneg
    (f := fun x ↦ input x * channel.transition x output)
    (fun x _ ↦ mul_nonneg (input.nonnegative x) (channel.nonnegative x output))]
  apply Finset.sum_congr rfl
  intro x _
  exact ENNReal.ofReal_mul (input.nonnegative x)

/-- Serial channel composition agrees with mathlib's PMF bind. -/
@[simp, capacity_shared_api]
theorem toPMF_comp (next : FiniteChannel Y Z) (channel : FiniteChannel X Y) (input : X) :
    (next.comp channel).toPMF input = (channel.toPMF input).bind next.toPMF := by
  ext output
  simp only [toPMF_apply, comp, PMF.bind_apply, tsum_fintype]
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun y _ ↦ mul_nonneg (channel.nonnegative input y) (next.nonnegative y output))]
  apply Finset.sum_congr rfl
  intro y _
  exact ENNReal.ofReal_mul (channel.nonnegative input y)

end CapacityAtlas.FiniteChannel
