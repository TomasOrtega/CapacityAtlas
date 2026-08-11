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
@[capacity_problem "noiseless-q-ary-channel", capacity_statement]
theorem noiseless_informationCapacity (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] :
    (FiniteChannel.identity X).informationCapacityBits =
      Real.log (Fintype.card X) / Real.log 2 := by
  apply FiniteChannel.informationCapacityBits_eq_of_upper_bound_attained
    (FiniteChannel.identity X) (Real.log (Fintype.card X) / Real.log 2)
    (FiniteDistribution.uniform X)
  · intro input
    rw [FiniteChannel.mutualInformationBits, identity_mutualInformation]
    exact div_le_div_of_nonneg_right input.entropy_le_log_card
      (Real.log_pos (by norm_num)).le
  · rw [FiniteChannel.mutualInformationBits, identity_mutualInformation,
      FiniteDistribution.entropy_uniform]

/-- The operational average-error capacity claim for a noiseless `q`-symbol channel. -/
@[capacity_problem "noiseless-q-ary-channel", capacity_statement]
def noiselessCapacityStatement (q : ℕ) (_hq : 2 ≤ q) : Prop :=
  (FiniteChannel.identity (Fin q)).operationalCapacityBits =
    Real.log q / Real.log 2

/-- The operational average-error capacity of a noiseless finite channel. -/
@[capacity_problem "noiseless-q-ary-channel", capacity_short_proof]
theorem noiseless_operationalCapacity (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] :
    (FiniteChannel.identity X).operationalCapacityBits =
      Real.log (Fintype.card X) / Real.log 2 := by
  calc
    (FiniteChannel.identity X).operationalCapacityBits =
        (FiniteChannel.identity X).informationCapacityBits :=
      FiniteChannel.codingTheorem (FiniteChannel.identity X)
    _ = Real.log (Fintype.card X) / Real.log 2 := noiseless_informationCapacity X

/-- The registered noiseless-channel capacity proposition holds unconditionally. -/
@[capacity_problem "noiseless-q-ary-channel", capacity_short_proof]
theorem noiselessCapacityStatement_proof (q : ℕ) (hq : 2 ≤ q) :
    noiselessCapacityStatement q hq := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  letI : Nonempty (Fin q) := Fin.pos_iff_nonempty.mp hq0
  simpa [noiselessCapacityStatement] using noiseless_operationalCapacity (Fin q)

end CapacityAtlas.Channel
