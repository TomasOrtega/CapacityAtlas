/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteChannelCapacity
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact

open scoped BigOperators

namespace CapacityAtlas.FiniteChannel

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- A finite channel with a nonempty input alphabet admits a capacity-achieving input. -/
@[capacity_shared_api]
theorem exists_capacityAchieving_input [Nonempty X] (channel : FiniteChannel X Y) :
    ∃ input : FiniteDistribution X,
      channel.mutualInformationBits input = channel.informationCapacityBits := by
  classical
  have hnonempty : (stdSimplex ℝ X).Nonempty := by
    let input := FiniteDistribution.uniform X
    exact ⟨input, input.nonnegative, input.sum_probability⟩
  let information : (X → ℝ) → ℝ := fun p ↦
    ((∑ y, Real.negMulLog (∑ x, p x * channel.transition x y)) -
      ∑ x, p x * (channel.rowDistribution x).entropy) / Real.log 2
  have hcontinuous : Continuous information := by
    dsimp [information]
    fun_prop
  obtain ⟨p, hp, hmax⟩ :=
    (isCompact_stdSimplex ℝ X).exists_isMaxOn hnonempty hcontinuous.continuousOn
  let input : FiniteDistribution X := ⟨p, hp.1, hp.2⟩
  refine ⟨input, (channel.informationCapacityBits_eq_of_upper_bound_attained
    (channel.mutualInformationBits input) input ?_ rfl).symm⟩
  intro other
  exact hmax ⟨other.nonnegative, other.sum_probability⟩

end CapacityAtlas.FiniteChannel
