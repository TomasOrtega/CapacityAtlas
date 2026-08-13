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

namespace CapacityAtlas.Channel

open CapacityAtlas

private theorem identity_outputDistribution {X : Type*} [Fintype X] [DecidableEq X]
    (input : FiniteDistribution X) :
    (FiniteChannel.identity X).outputDistribution input = input := by
  ext output
  simp [FiniteChannel.outputDistribution_apply, FiniteChannel.identity]

private theorem identity_rowDistribution_entropy {X : Type*} [Fintype X] [DecidableEq X]
    (input : X) :
    ((FiniteChannel.identity X).rowDistribution input).entropy = 0 := by
  apply Finset.sum_eq_zero
  intro output _
  change Real.negMulLog (if input = output then 1 else 0) = 0
  by_cases h : input = output <;> simp [h, Real.negMulLog_def]

private theorem identity_mutualInformation {X : Type*} [Fintype X] [DecidableEq X]
    (input : FiniteDistribution X) :
    (FiniteChannel.identity X).mutualInformation input = input.entropy := by
  rw [FiniteChannel.mutualInformation, identity_outputDistribution]
  simp [FiniteChannel.conditionalOutputEntropy, identity_rowDistribution_entropy]

/-- The single-letter information capacity of a noiseless finite channel. -/
@[capacity_problem "noiseless-q-ary-channel", capacity_statement, capacity_solved,
  capacity_formal_proof, capacity_claim "information-capacity" 1]
theorem noiseless_informationCapacity (q : ℕ) (hq : 2 ≤ q) :
    (FiniteChannel.identity (Fin q)).informationCapacityBits = Real.log q / Real.log 2 := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  letI : Nonempty (Fin q) := Fin.pos_iff_nonempty.mp hq0
  apply FiniteChannel.informationCapacityBits_eq_of_upper_bound_attained
    (FiniteChannel.identity (Fin q)) (Real.log q / Real.log 2)
    (FiniteDistribution.uniform (Fin q))
  · intro input
    rw [FiniteChannel.mutualInformationBits, identity_mutualInformation]
    exact div_le_div_of_nonneg_right (by simpa using input.entropy_le_log_card)
      (Real.log_pos (by norm_num)).le
  · rw [FiniteChannel.mutualInformationBits, identity_mutualInformation,
      FiniteDistribution.entropy_uniform, Fintype.card_fin]

/-- The operational average-error capacity of a noiseless finite channel. -/
@[capacity_problem "noiseless-q-ary-channel", capacity_statement, capacity_solved,
  capacity_formal_proof, capacity_claim "operational-capacity" 1]
theorem noiseless_operationalCapacity (q : ℕ) (hq : 2 ≤ q) :
    (FiniteChannel.identity (Fin q)).operationalCapacityBits = Real.log q / Real.log 2 := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  letI : Nonempty (Fin q) := Fin.pos_iff_nonempty.mp hq0
  calc
    (FiniteChannel.identity (Fin q)).operationalCapacityBits =
        (FiniteChannel.identity (Fin q)).informationCapacityBits :=
      FiniteChannel.codingTheorem (FiniteChannel.identity (Fin q))
    _ = Real.log q / Real.log 2 := noiseless_informationCapacity q hq

end CapacityAtlas.Channel
