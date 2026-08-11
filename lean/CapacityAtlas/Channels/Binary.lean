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

import CapacityAtlasForMathlib.InformationTheory.BinarySymmetric
import CapacityAtlasForMathlib.InformationTheory.CodingConverse

namespace CapacityAtlas.Channel

open CapacityAtlas

/-- Transition probabilities of the binary symmetric channel. -/
def binarySymmetricTransition (p : ℝ) (input output : Bool) : ℝ :=
  if input = output then 1 - p else p

/-- The binary symmetric channel with crossover probability `p`. -/
@[capacity_problem "binary-symmetric-channel", capacity_definition]
def binarySymmetric (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    FiniteChannel Bool Bool where
  transition := binarySymmetricTransition p
  nonnegative input output := by
    simp only [binarySymmetricTransition]
    split
    · linarith
    · exact hp0
  row_sum input := by
    cases input <;> simp [binarySymmetricTransition]

/-- The BSC constructor has the shared binary-symmetric transition predicate. -/
@[capacity_problem "binary-symmetric-channel", capacity_short_proof]
theorem binarySymmetric_isBinarySymmetric (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binarySymmetric p hp0 hp1).IsBinarySymmetric p := by
  intro input output
  rfl

/-- The single-letter information capacity of the binary symmetric channel. -/
@[capacity_problem "binary-symmetric-channel", capacity_statement]
theorem binarySymmetric_informationCapacity (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binarySymmetric p hp0 hp1).informationCapacityBits =
      1 - Real.binEntropy p / Real.log 2 :=
  FiniteChannel.informationCapacityBits_eq_binarySymmetric
    (binarySymmetric_isBinarySymmetric p hp0 hp1) hp0 hp1

/-- The noiseless BSC has information capacity one bit per use. -/
@[capacity_problem "binary-symmetric-channel", capacity_short_proof]
theorem binarySymmetric_informationCapacity_zero :
    (binarySymmetric 0 (by norm_num) (by norm_num)).informationCapacityBits = 1 := by
  rw [binarySymmetric_informationCapacity]
  simp

/-- The completely noisy BSC has zero information capacity. -/
@[capacity_problem "binary-symmetric-channel", capacity_short_proof]
theorem binarySymmetric_informationCapacity_half :
    (binarySymmetric 2⁻¹ (by norm_num) (by norm_num)).informationCapacityBits = 0 := by
  rw [binarySymmetric_informationCapacity, Real.binEntropy_two_inv]
  field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)]
  norm_num

/-- The operational average-error capacity claim for the BSC parameter range used by the atlas. -/
@[capacity_problem "binary-symmetric-channel", capacity_statement]
def binarySymmetricCapacityStatement (p : ℝ) (hp0 : 0 ≤ p) (hpHalf : p ≤ 2⁻¹) : Prop :=
  let channel := binarySymmetric p hp0 (hpHalf.trans (by norm_num))
  channel.operationalCapacityBits = 1 - Real.binEntropy p / Real.log 2

/-- The operational BSC formula follows from the finite-channel coding theorem. -/
@[capacity_problem "binary-symmetric-channel", capacity_short_proof]
theorem binarySymmetric_operationalCapacity_of_codingTheorem
    (p : ℝ) (hp0 : 0 ≤ p) (hpHalf : p ≤ 2⁻¹)
    (codingTheorem :
      (binarySymmetric p hp0 (hpHalf.trans (by norm_num))).SatisfiesCodingTheorem) :
    binarySymmetricCapacityStatement p hp0 hpHalf :=
  FiniteChannel.operationalCapacityBits_eq_of_satisfiesCodingTheorem _ _ codingTheorem
    (binarySymmetric_informationCapacity p hp0 (hpHalf.trans (by norm_num)))

/-- The operational average-error capacity of the binary symmetric channel. -/
@[capacity_problem "binary-symmetric-channel", capacity_short_proof]
theorem binarySymmetric_operationalCapacity
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binarySymmetric p hp0 hp1).operationalCapacityBits =
      1 - Real.binEntropy p / Real.log 2 := by
  calc
    (binarySymmetric p hp0 hp1).operationalCapacityBits =
        (binarySymmetric p hp0 hp1).informationCapacityBits :=
      FiniteChannel.codingTheorem (binarySymmetric p hp0 hp1)
    _ = 1 - Real.binEntropy p / Real.log 2 :=
      binarySymmetric_informationCapacity p hp0 hp1

/-- The registered BSC capacity proposition holds unconditionally. -/
@[capacity_problem "binary-symmetric-channel", capacity_short_proof]
theorem binarySymmetricCapacityStatement_proof
    (p : ℝ) (hp0 : 0 ≤ p) (hpHalf : p ≤ 2⁻¹) :
    binarySymmetricCapacityStatement p hp0 hpHalf :=
  binarySymmetric_operationalCapacity p hp0 (hpHalf.trans (by norm_num))

/-- At crossover probability zero, the binary symmetric channel is noiseless. -/
@[capacity_problem "binary-symmetric-channel", capacity_short_proof]
theorem binarySymmetric_zero :
    binarySymmetric 0 (by norm_num) (by norm_num) =
      FiniteChannel.identity Bool := by
  apply FiniteChannel.ext
  intro input output
  simp [binarySymmetric, binarySymmetricTransition, FiniteChannel.identity]

/-- Transition probabilities of the binary erasure channel.

`none` is the erasure symbol and `some bit` is an unerased output.
-/
def binaryErasureTransition (e : ℝ) (input : Bool) : Option Bool → ℝ
  | none => e
  | some output => if input = output then 1 - e else 0

/-- The binary erasure channel with erasure probability `e`. -/
@[capacity_problem "binary-erasure-channel", capacity_definition]
def binaryErasure (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    FiniteChannel Bool (Option Bool) where
  transition := binaryErasureTransition e
  nonnegative input output := by
    cases output with
    | none => exact he0
    | some output =>
        simp only [binaryErasureTransition]
        split
        · linarith
        · norm_num
  row_sum input := by
    cases input <;> simp [binaryErasureTransition]

/-- An erasure has probability `e` under every BEC input distribution. -/
theorem binaryErasure_outputDistribution_none
    (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) (input : FiniteDistribution Bool) :
    (binaryErasure e he0 he1).outputDistribution input none = e := by
  change (∑ symbol, input symbol * e) = e
  rw [← Finset.sum_mul, show (∑ symbol, input symbol) = 1 from input.sum_probability,
    one_mul]

/-- An unerased BEC output retains its input mass, scaled by `1 - e`. -/
theorem binaryErasure_outputDistribution_some
    (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (input : FiniteDistribution Bool) (output : Bool) :
    (binaryErasure e he0 he1).outputDistribution input (some output) =
      (1 - e) * input output := by
  cases output <;>
    simp [FiniteChannel.outputDistribution_apply, binaryErasure,
      binaryErasureTransition, input.bool_probability_false] <;> ring

/-- Every BEC row has binary entropy `h(e)`. -/
theorem binaryErasure_rowDistribution_entropy
    (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) (input : Bool) :
    ((binaryErasure e he0 he1).rowDistribution input).entropy =
      Real.binEntropy e := by
  change (∑ output : Option Bool, Real.negMulLog (binaryErasureTransition e input output)) =
    Real.binEntropy e
  rw [Fintype.sum_option]
  cases input <;>
    simp [binaryErasureTransition, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

/-- The BEC conditional output entropy is independent of the input distribution. -/
theorem binaryErasure_conditionalOutputEntropy
    (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) (input : FiniteDistribution Bool) :
    (binaryErasure e he0 he1).conditionalOutputEntropy input =
      Real.binEntropy e := by
  unfold FiniteChannel.conditionalOutputEntropy
  simp_rw [binaryErasure_rowDistribution_entropy]
  rw [← Finset.sum_mul, show (∑ symbol, input symbol) = 1 from input.sum_probability,
    one_mul]

/-- The BEC output entropy splits into erasure entropy and retained input entropy. -/
theorem binaryErasure_outputEntropy
    (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) (input : FiniteDistribution Bool) :
    ((binaryErasure e he0 he1).outputDistribution input).entropy =
      Real.binEntropy e + (1 - e) * input.entropy := by
  unfold FiniteDistribution.entropy
  rw [Fintype.sum_option, binaryErasure_outputDistribution_none]
  simp_rw [binaryErasure_outputDistribution_some, Real.negMulLog_mul]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul,
    show (∑ symbol, input symbol) = 1 from input.sum_probability, one_mul, ← Finset.mul_sum]
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

/-- The BEC retains the fraction `1 - e` of the input entropy. -/
theorem binaryErasure_mutualInformation
    (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) (input : FiniteDistribution Bool) :
    (binaryErasure e he0 he1).mutualInformation input =
      (1 - e) * input.entropy := by
  rw [FiniteChannel.mutualInformation, binaryErasure_outputEntropy,
    binaryErasure_conditionalOutputEntropy]
  ring

/-- The single-letter information capacity of the binary erasure channel. -/
@[capacity_problem "binary-erasure-channel", capacity_statement]
theorem binaryErasure_informationCapacity (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    (binaryErasure e he0 he1).informationCapacityBits = 1 - e := by
  let uniform := FiniteDistribution.uniform Bool
  apply FiniteChannel.informationCapacityBits_eq_of_upper_bound_attained
    (binaryErasure e he0 he1) (1 - e) uniform
  · intro input
    rw [FiniteChannel.mutualInformationBits, binaryErasure_mutualInformation]
    have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hentropy : input.entropy ≤ Real.log 2 := by
      simpa using input.entropy_le_log_card
    apply (div_le_iff₀ hlogTwo).2
    nlinarith
  · rw [FiniteChannel.mutualInformationBits, binaryErasure_mutualInformation,
      FiniteDistribution.entropy_uniform]
    norm_num

/-- The operational average-error capacity claim for the binary erasure channel. -/
@[capacity_problem "binary-erasure-channel", capacity_statement]
def binaryErasureCapacityStatement (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) : Prop :=
  (binaryErasure e he0 he1).operationalCapacityBits = 1 - e

/-- The operational BEC formula follows from the finite-channel coding theorem. -/
@[capacity_problem "binary-erasure-channel", capacity_short_proof]
theorem binaryErasure_operationalCapacity_of_codingTheorem
    (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (codingTheorem : (binaryErasure e he0 he1).SatisfiesCodingTheorem) :
    binaryErasureCapacityStatement e he0 he1 :=
  FiniteChannel.operationalCapacityBits_eq_of_satisfiesCodingTheorem _ _ codingTheorem
    (binaryErasure_informationCapacity e he0 he1)

/-- The operational average-error capacity of the binary erasure channel. -/
@[capacity_problem "binary-erasure-channel", capacity_short_proof]
theorem binaryErasure_operationalCapacity (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    (binaryErasure e he0 he1).operationalCapacityBits = 1 - e := by
  calc
    (binaryErasure e he0 he1).operationalCapacityBits =
        (binaryErasure e he0 he1).informationCapacityBits :=
      FiniteChannel.codingTheorem (binaryErasure e he0 he1)
    _ = 1 - e := binaryErasure_informationCapacity e he0 he1

/-- The registered BEC capacity proposition holds unconditionally. -/
@[capacity_problem "binary-erasure-channel", capacity_short_proof]
theorem binaryErasureCapacityStatement_proof
    (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    binaryErasureCapacityStatement e he0 he1 :=
  binaryErasure_operationalCapacity e he0 he1

/-- Transition probabilities of the binary Z-channel.

Input `false` is transmitted without error. Input `true` changes to `false`
with probability `p`.
-/
def binaryZTransition (p : ℝ) (input output : Bool) : ℝ :=
  match input, output with
  | false, false => 1
  | false, true => 0
  | true, false => p
  | true, true => 1 - p

/-- The binary Z-channel with crossover probability `p`. -/
@[capacity_problem "binary-z-channel", capacity_definition]
def binaryZ (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    FiniteChannel Bool Bool where
  transition := binaryZTransition p
  nonnegative input output := by
    cases input <;> cases output <;> simp [binaryZTransition] <;> linarith
  row_sum input := by
    cases input <;> simp [binaryZTransition]

end CapacityAtlas.Channel
