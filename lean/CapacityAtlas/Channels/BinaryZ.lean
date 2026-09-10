/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlas.Channels.Binary
import CapacityAtlasForMathlib.InformationTheory.BinaryEntropyOptimization

namespace CapacityAtlas.Channel

/-- Probability of input `true` in a capacity-achieving Z-channel input.

Lean's totalized powers and division give `1/2` at `p = 0` and `1` at `p = 1`.
The latter endpoint has constant output, so every input is optimal.
-/
@[capacity_problem "binary-z-channel", capacity_definition]
noncomputable def binaryZOptimalBias (p : ℝ) : ℝ :=
  p ^ (p / (1 - p)) / (1 + (1 - p) * p ^ (p / (1 - p)))

/-- The explicit optimizing bias is a probability, including both endpoints. -/
@[capacity_api]
theorem binaryZOptimalBias_mem (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ binaryZOptimalBias p ∧ binaryZOptimalBias p ≤ 1 := by
  have hr0 := Real.rpow_nonneg hp0 (p / (1 - p))
  have hr1 := Real.rpow_le_one hp0 hp1 (div_nonneg hp0 (sub_nonneg.mpr hp1))
  have ht0 := mul_nonneg (sub_nonneg.mpr hp1) hr0
  unfold binaryZOptimalBias
  exact ⟨div_nonneg hr0 (by positivity), (div_le_one (by positivity)).2 (by linarith)⟩

/-- An explicit capacity-achieving Bernoulli input for the Z-channel. -/
@[capacity_problem "binary-z-channel", capacity_definition]
noncomputable def binaryZOptimalInput (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    FiniteDistribution Bool :=
  FiniteDistribution.bernoulli (binaryZOptimalBias p)
    (binaryZOptimalBias_mem p hp0 hp1).1 (binaryZOptimalBias_mem p hp0 hp1).2

/-- The Z-channel mutual information is a one-variable binary-entropy objective. -/
@[capacity_api]
theorem binaryZ_mutualInformation (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (input : FiniteDistribution Bool) :
    (binaryZ p hp0 hp1).mutualInformation input =
      Real.binEntropy ((1 - p) * input true) - input true * Real.binEntropy p := by
  rw [FiniteChannel.mutualInformation, FiniteDistribution.entropy_bool]
  simp [FiniteChannel.conditionalOutputEntropy, FiniteDistribution.entropy_bool,
    binaryZ, binaryZTransition, Real.binEntropy_one_sub, mul_comm]

private theorem binaryZ_entropy_coefficient (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Real.binEntropy p =
      -(1 - p) * Real.log ((1 - p) * p ^ (p / (1 - p))) := by
  rw [Real.log_mul (sub_pos.mpr hp1).ne' (Real.rpow_pos_of_pos hp0 _).ne',
    Real.log_rpow hp0, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Real.negMulLog_def]
  field_simp [(sub_pos.mpr hp1).ne'] <;> ring

/-- For an interior parameter, the binary entropy bound is attained by the explicit input. -/
@[capacity_api]
theorem binaryZ_mutualInformation_optimum (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ input, (binaryZ p hp0.le hp1.le).mutualInformation input ≤
      Real.log (1 + (1 - p) * p ^ (p / (1 - p)))) ∧
    (binaryZ p hp0.le hp1.le).mutualInformation (binaryZOptimalInput p hp0.le hp1.le) =
      Real.log (1 + (1 - p) * p ^ (p / (1 - p))) := by
  let t := (1 - p) * p ^ (p / (1 - p))
  have ht : 0 < t := mul_pos (sub_pos.mpr hp1) (Real.rpow_pos_of_pos hp0 _)
  have hentropy := binaryZ_entropy_coefficient p hp0 hp1
  constructor
  · intro input
    rw [binaryZ_mutualInformation, hentropy]
    have hx0 : 0 ≤ (1 - p) * input true :=
      mul_nonneg (sub_nonneg.mpr hp1.le) (input.nonnegative true)
    have hx1 : (1 - p) * input true ≤ 1 :=
      (mul_le_mul_of_nonneg_left (input.probability_le_one true)
        (sub_nonneg.mpr hp1.le)).trans (by linarith)
    convert Real.binEntropy_add_mul_log_le_log_one_add hx0 hx1 ht using 1 <;> dsimp [t] <;> ring
  · rw [binaryZ_mutualInformation, hentropy]
    change Real.binEntropy ((1 - p) * binaryZOptimalBias p) -
      binaryZOptimalBias p * (-(1 - p) * Real.log t) = Real.log (1 + t)
    have hbias : (1 - p) * binaryZOptimalBias p = t / (1 + t) := by
      dsimp [binaryZOptimalBias, t]
      ring
    calc
      _ = Real.binEntropy ((1 - p) * binaryZOptimalBias p) +
          ((1 - p) * binaryZOptimalBias p) * Real.log t := by ring
      _ = Real.log (1 + t) := by
        rw [hbias]
        exact Real.binEntropy_div_one_add_add_mul_log ht

/-- The exact Z-channel information capacity, with both endpoints included explicitly. -/
@[capacity_problem "binary-z-channel", capacity_statement, capacity_solved,
  capacity_formal_proof, capacity_claim "information-capacity" 1]
theorem binaryZ_informationCapacity (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binaryZ p hp0 hp1).informationCapacityBits =
      Real.log (1 + (1 - p) * p ^ (p / (1 - p))) / Real.log 2 := by
  apply FiniteChannel.informationCapacityBits_eq_of_upper_bound_attained
    (binaryZ p hp0 hp1) _ (binaryZOptimalInput p hp0 hp1)
  · intro input
    rcases eq_or_lt_of_le hp0 with rfl | hp0'
    · rw [FiniteChannel.mutualInformationBits, binaryZ_mutualInformation]
      simpa using (div_le_div_of_nonneg_right (Real.binEntropy_le_log_two
        (p := input true)) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)
    rcases eq_or_lt_of_le hp1 with rfl | hp1'
    · simp [FiniteChannel.mutualInformationBits, binaryZ_mutualInformation]
    exact div_le_div_of_nonneg_right
      ((binaryZ_mutualInformation_optimum p hp0' hp1').1 input)
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  · rcases eq_or_lt_of_le hp0 with rfl | hp0'
    · norm_num [FiniteChannel.mutualInformationBits, binaryZ_mutualInformation,
        binaryZOptimalInput, binaryZOptimalBias, Real.binEntropy_two_inv]
    rcases eq_or_lt_of_le hp1 with rfl | hp1'
    · simp [FiniteChannel.mutualInformationBits, binaryZ_mutualInformation]
    exact congrArg (fun value ↦ value / Real.log 2)
      (binaryZ_mutualInformation_optimum p hp0' hp1').2

/-- The operational average-error capacity follows from the finite-DMC coding theorem. -/
@[capacity_problem "binary-z-channel", capacity_statement, capacity_solved,
  capacity_formal_proof, capacity_claim "operational-capacity" 1]
theorem binaryZ_operationalCapacity (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binaryZ p hp0 hp1).operationalCapacityBits =
      Real.log (1 + (1 - p) * p ^ (p / (1 - p))) / Real.log 2 := by
  rw [FiniteChannel.codingTheorem, binaryZ_informationCapacity]

/-- The stated Bernoulli input attains the operational capacity for every parameter. -/
@[capacity_problem "binary-z-channel", capacity_statement, capacity_solved,
  capacity_formal_proof, capacity_claim "optimizing-input" 1]
theorem binaryZ_optimalInput (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binaryZ p hp0 hp1).mutualInformationBits (binaryZOptimalInput p hp0 hp1) =
      (binaryZ p hp0 hp1).operationalCapacityBits := by
  rw [binaryZ_operationalCapacity]
  rcases eq_or_lt_of_le hp0 with rfl | hp0'
  · norm_num [FiniteChannel.mutualInformationBits, binaryZ_mutualInformation,
      binaryZOptimalInput, binaryZOptimalBias, Real.binEntropy_two_inv]
  rcases eq_or_lt_of_le hp1 with rfl | hp1'
  · simp [FiniteChannel.mutualInformationBits, binaryZ_mutualInformation]
  exact congrArg (fun value ↦ value / Real.log 2)
    (binaryZ_mutualInformation_optimum p hp0' hp1').2

/-- The noiseless endpoint has capacity one bit per use and uses a uniform input. -/
@[capacity_problem "binary-z-channel", capacity_test]
theorem binaryZ_zero :
    (binaryZ 0 (by norm_num) (by norm_num)).operationalCapacityBits = 1 ∧
      binaryZOptimalInput 0 (by norm_num) (by norm_num) = FiniteDistribution.uniform Bool := by
  constructor
  · rw [binaryZ_operationalCapacity]
    norm_num
  · ext input
    cases input <;> norm_num [binaryZOptimalInput, binaryZOptimalBias]

/-- The constant-output endpoint has zero capacity, attained by every input distribution. -/
@[capacity_problem "binary-z-channel", capacity_test]
theorem binaryZ_one (input : FiniteDistribution Bool) :
    (binaryZ 1 (by norm_num) (by norm_num)).operationalCapacityBits = 0 ∧
      (binaryZ 1 (by norm_num) (by norm_num)).mutualInformationBits input = 0 := by
  simp [binaryZ_operationalCapacity, FiniteChannel.mutualInformationBits,
    binaryZ_mutualInformation]

end CapacityAtlas.Channel
