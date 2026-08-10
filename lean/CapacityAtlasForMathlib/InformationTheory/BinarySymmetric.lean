/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteChannelCapacity

namespace CapacityAtlas

namespace FiniteChannel

/-- Probability of output `true` when a Bernoulli-`q` input passes through a binary
symmetric channel with crossover probability `p`. -/
@[capacity_shared_api]
def binarySymmetricOutputBias (p q : ℝ) : ℝ :=
  (1 - q) * p + q * (1 - p)

variable (channel : FiniteChannel Bool Bool) (p : ℝ)

/-- A finite channel has binary-symmetric transition probabilities with parameter `p`. -/
@[capacity_shared_api]
def IsBinarySymmetric : Prop :=
  ∀ input output, channel.transition input output = if input = output then 1 - p else p

variable {channel p}
variable {q : ℝ}

@[capacity_shared_api]
theorem binarySymmetricOutputBias_nonnegative
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ binarySymmetricOutputBias p q := by
  unfold binarySymmetricOutputBias
  positivity

@[capacity_shared_api]
theorem binarySymmetricOutputBias_le_one
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    binarySymmetricOutputBias p q ≤ 1 := by
  unfold binarySymmetricOutputBias
  nlinarith [mul_nonneg (sub_nonneg.mpr hq1) hp0,
    mul_nonneg hq0 (sub_nonneg.mpr hp1)]

@[capacity_shared_api]
theorem outputDistribution_eq_bernoulli (hchannel : channel.IsBinarySymmetric p)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (input : FiniteDistribution Bool) :
    channel.outputDistribution input =
      FiniteDistribution.bernoulli
        (binarySymmetricOutputBias p (input true))
        (binarySymmetricOutputBias_nonnegative hp0 hp1
          (input.nonnegative true) (input.probability_le_one true))
        (binarySymmetricOutputBias_le_one hp0 hp1
          (input.nonnegative true) (input.probability_le_one true)) := by
  apply FiniteDistribution.ext
  intro output
  cases output
  · simp only [outputDistribution_apply, Fintype.sum_bool,
      FiniteDistribution.bernoulli_false]
    rw [hchannel true false, hchannel false false, input.bool_probability_false]
    simp only [Bool.true_eq_false, ↓reduceIte]
    unfold binarySymmetricOutputBias
    ring
  · simp only [outputDistribution_apply, Fintype.sum_bool,
      FiniteDistribution.bernoulli_true]
    rw [hchannel true true, hchannel false true, input.bool_probability_false]
    simp only [↓reduceIte, Bool.false_eq_true]
    unfold binarySymmetricOutputBias
    ring

@[capacity_shared_api]
theorem entropy_rowDistribution_eq_binEntropy (hchannel : channel.IsBinarySymmetric p)
    (input : Bool) :
    (channel.rowDistribution input).entropy = Real.binEntropy p := by
  cases input
  · simp only [FiniteDistribution.entropy, Fintype.sum_bool, rowDistribution_apply]
    rw [hchannel false true, hchannel false false,
      Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp
  · simp only [FiniteDistribution.entropy, Fintype.sum_bool, rowDistribution_apply]
    rw [hchannel true true, hchannel true false,
      Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [↓reduceIte, Bool.true_eq_false]
    ac_rfl

@[capacity_shared_api]
theorem conditionalOutputEntropy_eq_binEntropy (hchannel : channel.IsBinarySymmetric p)
    (input : FiniteDistribution Bool) :
    channel.conditionalOutputEntropy input = Real.binEntropy p := by
  rw [conditionalOutputEntropy]
  simp only [Fintype.sum_bool, entropy_rowDistribution_eq_binEntropy hchannel]
  have hsum := input.sum_probability
  simp only [Fintype.sum_bool] at hsum
  have hsum' : input true + input false = 1 := hsum
  calc
    input true * Real.binEntropy p + input false * Real.binEntropy p =
        (input true + input false) * Real.binEntropy p := by ring
    _ = Real.binEntropy p := by rw [hsum', one_mul]

@[capacity_shared_api]
theorem mutualInformationBits_eq_binEntropy (hchannel : channel.IsBinarySymmetric p)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (input : FiniteDistribution Bool) :
    channel.mutualInformationBits input =
      Real.binEntropy (binarySymmetricOutputBias p (input true)) / Real.log 2 -
        Real.binEntropy p / Real.log 2 := by
  rw [mutualInformationBits, mutualInformation,
    outputDistribution_eq_bernoulli hchannel hp0 hp1 input,
    FiniteDistribution.entropy_bernoulli,
    conditionalOutputEntropy_eq_binEntropy hchannel]
  ring

/-- The single-letter information capacity of any binary symmetric finite channel. -/
@[capacity_shared_api]
theorem informationCapacityBits_eq_binarySymmetric (hchannel : channel.IsBinarySymmetric p)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    channel.informationCapacityBits = 1 - Real.binEntropy p / Real.log 2 := by
  let uniform := FiniteDistribution.bernoulli (2 : ℝ)⁻¹ (by positivity) (by norm_num)
  apply informationCapacityBits_eq_of_upper_bound_attained channel
    (1 - Real.binEntropy p / Real.log 2) uniform
  · intro input
    rw [mutualInformationBits_eq_binEntropy hchannel hp0 hp1]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hentropy := Real.binEntropy_le_log_two
      (p := binarySymmetricOutputBias p (input true))
    have hnormalized :
        Real.binEntropy (binarySymmetricOutputBias p (input true)) / Real.log 2 ≤ 1 :=
      (div_le_one hlog).2 hentropy
    linarith
  · rw [mutualInformationBits_eq_binEntropy hchannel hp0 hp1]
    have hbias : binarySymmetricOutputBias p (uniform true) = (2 : ℝ)⁻¹ := by
      simp [uniform, binarySymmetricOutputBias]
      ring
    rw [hbias, Real.binEntropy_two_inv]
    field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)]

end FiniteChannel

end CapacityAtlas
