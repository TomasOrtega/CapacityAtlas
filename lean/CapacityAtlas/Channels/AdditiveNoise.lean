/-
Copyright 2026 The Capacity Atlas Authors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import CapacityAtlasForMathlib.InformationTheory.CodingConverse

open scoped BigOperators

namespace CapacityAtlas.Channel

open CapacityAtlas

variable {G : Type*} [Fintype G] [AddGroup G]

/-- The additive channel whose output is the input plus independent group-valued noise. -/
@[capacity_problem "finite-group-additive-noise-channel", capacity_definition]
def additiveNoise (noise : FiniteDistribution G) : FiniteChannel G G where
  transition input output := noise (-input + output)
  nonnegative input output := noise.nonnegative (-input + output)
  row_sum input := by
    change (∑ output, noise ((Equiv.addLeft (-input)) output)) = 1
    rw [Equiv.sum_comp (Equiv.addLeft (-input)) (fun z => noise z)]
    exact noise.sum_probability

/-- Every row of an additive-noise channel has the noise entropy. -/
theorem additiveNoise_rowDistribution_entropy (noise : FiniteDistribution G) (input : G) :
    ((additiveNoise noise).rowDistribution input).entropy = noise.entropy := by
  unfold FiniteDistribution.entropy
  change (∑ output, Real.negMulLog (noise ((Equiv.addLeft (-input)) output))) = _
  rw [Equiv.sum_comp (Equiv.addLeft (-input)) (fun z => Real.negMulLog (noise z))]

/-- Additive-noise conditional output entropy is independent of the input distribution. -/
theorem additiveNoise_conditionalOutputEntropy
    (noise : FiniteDistribution G) (input : FiniteDistribution G) :
    (additiveNoise noise).conditionalOutputEntropy input = noise.entropy := by
  unfold FiniteChannel.conditionalOutputEntropy
  simp_rw [additiveNoise_rowDistribution_entropy]
  rw [← Finset.sum_mul, show (∑ symbol, input symbol) = 1 from input.sum_probability,
    one_mul]

private def negAddRightEquiv (output : G) : G ≃ G :=
  (Equiv.neg G).trans (Equiv.addRight output)

/-- Uniform input produces uniform output through an additive-noise channel. -/
theorem additiveNoise_outputDistribution_uniform (noise : FiniteDistribution G) :
    (additiveNoise noise).outputDistribution (FiniteDistribution.uniform G) =
      FiniteDistribution.uniform G := by
  apply FiniteDistribution.ext
  intro output
  change (∑ input, (Fintype.card G : ℝ)⁻¹ * noise (-input + output)) =
    (Fintype.card G : ℝ)⁻¹
  rw [← Finset.mul_sum]
  have hsum : (∑ input, noise (-input + output)) = ∑ z, noise z := by
    exact (negAddRightEquiv output).sum_comp noise
  rw [hsum, show (∑ z, noise z) = 1 from noise.sum_probability, mul_one]

private theorem additiveNoise_informationCapacity_nats (noise : FiniteDistribution G) :
    (additiveNoise noise).informationCapacityBits =
      (Real.log (Fintype.card G) - noise.entropy) / Real.log 2 := by
  let uniform := FiniteDistribution.uniform G
  apply FiniteChannel.informationCapacityBits_eq_of_upper_bound_attained
    (additiveNoise noise)
    ((Real.log (Fintype.card G) - noise.entropy) / Real.log 2) uniform
  · intro input
    rw [FiniteChannel.mutualInformationBits, FiniteChannel.mutualInformation,
      additiveNoise_conditionalOutputEntropy]
    exact div_le_div_of_nonneg_right
      (sub_le_sub_right ((additiveNoise noise).outputDistribution input).entropy_le_log_card _)
      (Real.log_pos (by norm_num)).le
  · rw [FiniteChannel.mutualInformationBits, FiniteChannel.mutualInformation,
      additiveNoise_conditionalOutputEntropy, additiveNoise_outputDistribution_uniform,
      FiniteDistribution.entropy_uniform]

/-- The single-letter information capacity of a finite-group additive-noise channel. -/
@[capacity_problem "finite-group-additive-noise-channel", capacity_statement]
theorem additiveNoise_informationCapacity (noise : FiniteDistribution G) :
    (additiveNoise noise).informationCapacityBits =
      Real.log (Fintype.card G) / Real.log 2 - noise.entropyBits := by
  rw [additiveNoise_informationCapacity_nats, FiniteDistribution.entropyBits]
  ring

/-- The operational average-error capacity claim for a finite-group additive-noise channel. -/
@[capacity_problem "finite-group-additive-noise-channel", capacity_statement]
def finiteGroupAdditiveNoiseCapacityStatement (noise : FiniteDistribution G) : Prop :=
  (additiveNoise noise).operationalCapacityBits =
    Real.log (Fintype.card G) / Real.log 2 - noise.entropyBits

/-- The operational capacity of a finite-group additive-noise channel. -/
@[capacity_problem "finite-group-additive-noise-channel", capacity_short_proof]
theorem additiveNoise_operationalCapacity (noise : FiniteDistribution G) :
    (additiveNoise noise).operationalCapacityBits =
      Real.log (Fintype.card G) / Real.log 2 - noise.entropyBits := by
  calc
    (additiveNoise noise).operationalCapacityBits =
        (additiveNoise noise).informationCapacityBits :=
      FiniteChannel.codingTheorem (additiveNoise noise)
    _ = Real.log (Fintype.card G) / Real.log 2 - noise.entropyBits :=
      additiveNoise_informationCapacity noise

/-- The registered finite-group additive-noise proposition holds unconditionally. -/
@[capacity_problem "finite-group-additive-noise-channel", capacity_short_proof]
theorem finiteGroupAdditiveNoiseCapacityStatement_proof (noise : FiniteDistribution G) :
    finiteGroupAdditiveNoiseCapacityStatement noise :=
  additiveNoise_operationalCapacity noise

end CapacityAtlas.Channel
