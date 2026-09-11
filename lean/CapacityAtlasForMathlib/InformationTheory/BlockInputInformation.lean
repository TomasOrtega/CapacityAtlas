/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteEntropy
import CapacityAtlasForMathlib.InformationTheory.FiniteMixture

open scoped BigOperators

namespace CapacityAtlas

namespace FiniteDistribution

variable {X : Type*} [Fintype X] {n : ℕ} [NeZero n]

/-- The input law obtained by selecting a uniformly random coordinate of a word. -/
@[capacity_shared_api]
noncomputable def averageCoordinateMarginal
    (input : FiniteDistribution (Fin n → X)) : FiniteDistribution X :=
  mixture (uniform (Fin n)) input.coordinateMarginal

@[simp, capacity_shared_api]
theorem averageCoordinateMarginal_apply
    (input : FiniteDistribution (Fin n → X)) (x : X) :
    input.averageCoordinateMarginal x =
      (n : ℝ)⁻¹ * ∑ coordinate : Fin n, input.coordinateMarginal coordinate x := by
  simp [averageCoordinateMarginal, ← Finset.mul_sum]

end FiniteDistribution

namespace FiniteChannel

variable {X Y : Type*} [Fintype X] [Fintype Y] {n : ℕ} [NeZero n]

/-- Concavity bounds the coordinate information sum using their common average input law. -/
@[capacity_shared_api]
theorem sum_coordinate_mutualInformation_le_mul_averageCoordinateMarginal
    (channel : FiniteChannel X Y) (input : FiniteDistribution (Fin n → X)) :
    (∑ coordinate : Fin n, channel.mutualInformation (input.coordinateMarginal coordinate)) ≤
      (n : ℝ) * channel.mutualInformation input.averageCoordinateMarginal := by
  have hconcave :
      (n : ℝ)⁻¹ *
          (∑ coordinate : Fin n,
            channel.mutualInformation (input.coordinateMarginal coordinate)) ≤
        channel.mutualInformation input.averageCoordinateMarginal := by
    simpa [FiniteDistribution.averageCoordinateMarginal, ← Finset.mul_sum] using
      channel.mutualInformation_mixture_ge
        (FiniteDistribution.uniform (Fin n)) input.coordinateMarginal
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  simpa [← mul_assoc, hn] using
    mul_le_mul_of_nonneg_left hconcave (Nat.cast_nonneg n)

/-- The same averaged input law bounds block information for every memoryless channel. -/
@[capacity_shared_api]
theorem block_mutualInformation_le_mul_averageCoordinateMarginal
    (channel : FiniteChannel X Y) (input : FiniteDistribution (Fin n → X)) :
    (channel.block n).mutualInformation input ≤
      (n : ℝ) * channel.mutualInformation input.averageCoordinateMarginal :=
  (channel.block_mutualInformation_le_sum_coordinate n input).trans
    (channel.sum_coordinate_mutualInformation_le_mul_averageCoordinateMarginal input)

@[capacity_shared_api]
theorem block_mutualInformationBits_le_mul_averageCoordinateMarginal
    (channel : FiniteChannel X Y) (input : FiniteDistribution (Fin n → X)) :
    (channel.block n).mutualInformationBits input ≤
      (n : ℝ) * channel.mutualInformationBits input.averageCoordinateMarginal := by
  simpa only [mutualInformationBits, mul_div_assoc] using
    div_le_div_of_nonneg_right
      (channel.block_mutualInformation_le_mul_averageCoordinateMarginal input)
      (Real.log_nonneg (by norm_num))

end FiniteChannel

end CapacityAtlas
