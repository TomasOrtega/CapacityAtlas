/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteEntropy
import CapacityAtlasForMathlib.InformationTheory.RandomCoding

open scoped BigOperators

namespace CapacityAtlas

namespace FiniteChannel

variable {M X Y : Type*} [Fintype M] [Fintype X] [Fintype Y]

/-- A channel with its input symbols selected by a deterministic encoder. -/
@[capacity_shared_api]
def encoded (channel : FiniteChannel X Y) (encode : M → X) : FiniteChannel M Y where
  transition message output := channel.transition (encode message) output
  nonnegative message output := channel.nonnegative (encode message) output
  row_sum message := channel.row_sum (encode message)

@[simp, capacity_shared_api]
theorem encoded_transition (channel : FiniteChannel X Y) (encode : M → X)
    (message : M) (output : Y) :
    (channel.encoded encode).transition message output =
      channel.transition (encode message) output :=
  rfl

/-- Encoding before a channel is equivalent to pushing the input distribution forward. -/
@[capacity_shared_api]
theorem encoded_mutualInformation
    [DecidableEq X]
    (channel : FiniteChannel X Y) (encode : M → X) (input : FiniteDistribution M) :
    (channel.encoded encode).mutualInformation input =
      channel.mutualInformation (input.map encode) := by
  classical
  have houtput :
      (channel.encoded encode).outputDistribution input =
        channel.outputDistribution (input.map encode) := by
    apply FiniteDistribution.ext
    intro output
    change (∑ message, input message * channel.transition (encode message) output) =
      ∑ symbol, input.map encode symbol * channel.transition symbol output
    exact (input.sum_map_mul encode (fun symbol ↦ channel.transition symbol output)).symm
  have hconditional :
      (channel.encoded encode).conditionalOutputEntropy input =
        channel.conditionalOutputEntropy (input.map encode) := by
    unfold conditionalOutputEntropy
    simpa [encoded, rowDistribution] using
      (input.sum_map_mul encode
        (fun symbol ↦ (channel.rowDistribution symbol).entropy)).symm
  unfold mutualInformation
  rw [houtput, hconditional]

private noncomputable def identityEncoderCode [Nonempty M]
    (channel : FiniteChannel M Y) (decode : Y → M) : OneShotCode channel M where
  encode := id
  decode := decode

/-- Finite Fano inequality for a uniform message and deterministic decoder. -/
theorem fano_uniform [Nonempty M] [DecidableEq M]
    (channel : FiniteChannel M Y) (decode : Y → M) :
    Real.log (Fintype.card M) ≤
      channel.mutualInformation (FiniteDistribution.uniform M) + Real.log 2 +
        (identityEncoderCode channel decode).averageErrorProbability *
          Real.log (Fintype.card M) := by
  classical
  let uniform := FiniteDistribution.uniform M
  let joint : M → Y → ℝ := fun message output ↦
    uniform message * channel.transition message output
  let outputMass : Y → ℝ := fun output ↦ channel.outputDistribution uniform output
  let correct : Y → ℝ := fun output ↦ joint (decode output) output
  let error : Y → ℝ := fun output ↦
    ∑ message : M, if decode output ≠ message then joint message output else 0
  have hjointNonnegative (message : M) (output : Y) : 0 ≤ joint message output :=
    mul_nonneg (uniform.nonnegative message) (channel.nonnegative message output)
  have hcorrectNonnegative (output : Y) : 0 ≤ correct output :=
    hjointNonnegative _ _
  have herrorNonnegative (output : Y) : 0 ≤ error output := by
    exact Finset.sum_nonneg fun message _ ↦ by
      by_cases hmessage : decode output ≠ message
      · simp [hmessage, hjointNonnegative message output]
      · simp [hmessage]
  have hsplit (output : Y) : correct output + error output = outputMass output := by
    calc
      correct output + error output =
          ∑ message : M,
            ((if message = decode output then joint message output else 0) +
              if decode output ≠ message then joint message output else 0) := by
        unfold correct error
        rw [Finset.sum_add_distrib]
        simp
      _ = ∑ message : M, joint message output := by
        apply Fintype.sum_congr
        intro message
        by_cases hmessage : message = decode output
        · subst message
          simp
        · have hreverse : decode output ≠ message := Ne.symm hmessage
          simp [hmessage, hreverse]
      _ = outputMass output := by rfl
  have hwrongEntropy (output : Y) :
      (∑ message : M,
        Real.negMulLog (if decode output ≠ message then joint message output else 0)) ≤
        Real.negMulLog (error output) +
          error output * Real.log (Fintype.card M) := by
    simpa [error] using
      (FiniteDistribution.sum_negMulLog_le_negMulLog_sum_add_mul_log_card
        (fun message : M ↦ if decode output ≠ message then joint message output else 0)
        (fun message ↦ by
          by_cases hmessage : decode output ≠ message
          · simp [hmessage, hjointNonnegative message output]
          · simp [hmessage]))
  have hbinaryEntropy (output : Y) :
      Real.negMulLog (correct output) + Real.negMulLog (error output) ≤
        Real.negMulLog (outputMass output) + outputMass output * Real.log 2 := by
    let binaryWeight : Bool → ℝ := fun bit ↦ if bit then error output else correct output
    have hbinary :=
      FiniteDistribution.sum_negMulLog_le_negMulLog_sum_add_mul_log_card
        binaryWeight (fun bit ↦ by cases bit <;> simp [binaryWeight,
          hcorrectNonnegative output, herrorNonnegative output])
    simpa [binaryWeight, hsplit output, add_comm] using hbinary
  have hconditionalAt (output : Y) :
      (∑ message : M, Real.negMulLog (joint message output)) ≤
        Real.negMulLog (outputMass output) + outputMass output * Real.log 2 +
          error output * Real.log (Fintype.card M) := by
    have hdecompose :
        (∑ message : M, Real.negMulLog (joint message output)) =
          Real.negMulLog (correct output) +
            ∑ message : M,
              Real.negMulLog
                (if decode output ≠ message then joint message output else 0) := by
      calc
        ∑ message : M, Real.negMulLog (joint message output) =
            ∑ message : M,
              ((if message = decode output then Real.negMulLog (joint message output) else 0) +
                Real.negMulLog
                  (if decode output ≠ message then joint message output else 0)) := by
          apply Fintype.sum_congr
          intro message
          by_cases hmessage : message = decode output
          · subst message
            simp
          · have hreverse : decode output ≠ message := Ne.symm hmessage
            simp [hmessage, hreverse]
        _ = Real.negMulLog (correct output) +
            ∑ message : M,
              Real.negMulLog
                (if decode output ≠ message then joint message output else 0) := by
          rw [Finset.sum_add_distrib]
          simp [correct]
    rw [hdecompose]
    linarith [hwrongEntropy output, hbinaryEntropy output]
  have hglobalEntropy :
      (∑ output : Y, ∑ message : M, Real.negMulLog (joint message output)) ≤
        (∑ output : Y, Real.negMulLog (outputMass output)) + Real.log 2 +
          (∑ output : Y, error output) * Real.log (Fintype.card M) := by
    calc
      ∑ output : Y, ∑ message : M, Real.negMulLog (joint message output) ≤
          ∑ output : Y,
            (Real.negMulLog (outputMass output) + outputMass output * Real.log 2 +
              error output * Real.log (Fintype.card M)) :=
        Finset.sum_le_sum fun output _ ↦ hconditionalAt output
      _ = (∑ output : Y, Real.negMulLog (outputMass output)) + Real.log 2 +
          (∑ output : Y, error output) * Real.log (Fintype.card M) := by
        simp_rw [Finset.sum_add_distrib]
        have houtputSum : ∑ output : Y, outputMass output = 1 :=
          (channel.outputDistribution uniform).sum_probability
        rw [← Finset.sum_mul, houtputSum, one_mul, ← Finset.sum_mul]
  have hjointEntropy :
      (∑ output : Y, ∑ message : M, Real.negMulLog (joint message output)) =
        uniform.entropy + channel.conditionalOutputEntropy uniform := by
    rw [Finset.sum_comm]
    unfold joint conditionalOutputEntropy FiniteDistribution.entropy
    rw [← Finset.sum_add_distrib]
    apply Fintype.sum_congr
    intro message
    simp_rw [Real.negMulLog_mul]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, channel.row_sum message,
      one_mul, Finset.mul_sum]
    rfl
  have herrorTotal :
      ∑ output : Y, error output =
        (identityEncoderCode channel decode).averageErrorProbability := by
    rw [OneShotCode.averageErrorProbability_eq]
    unfold error
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    apply Fintype.sum_congr
    intro message
    rw [(identityEncoderCode channel decode).errorProbability_eq_sum_decode_ne]
    rw [Finset.mul_sum]
    apply Fintype.sum_congr
    intro output
    by_cases hdecode : decode output ≠ message <;>
      simp [joint, uniform, identityEncoderCode, hdecode]
  rw [hjointEntropy] at hglobalEntropy
  have houtputEntropy :
      (∑ output : Y, Real.negMulLog (outputMass output)) =
        (channel.outputDistribution uniform).entropy := by rfl
  have hfanoEntropy :
      uniform.entropy ≤ channel.mutualInformation uniform + Real.log 2 +
        (identityEncoderCode channel decode).averageErrorProbability *
          Real.log (Fintype.card M) := by
    unfold mutualInformation
    rw [houtputEntropy, herrorTotal] at hglobalEntropy
    linarith
  simpa [uniform, FiniteDistribution.entropy_uniform] using hfanoEntropy

/-- Fano and the block mutual-information bound control every finite block code. -/
@[capacity_shared_api]
theorem blockCode_log_messageCount_le
    (channel : FiniteChannel X Y) {blocklength : ℕ}
    (code : BlockCode channel blocklength) :
    Real.log code.messageCount ≤
      (blocklength : ℝ) * channel.informationCapacityBits * Real.log 2 + Real.log 2 +
        code.averageErrorProbability * Real.log code.messageCount := by
  classical
  letI : Nonempty (Fin code.messageCount) := Fin.pos_iff_nonempty.mp code.messageCount_pos
  let messageChannel := (channel.block blocklength).encoded code.encode
  have hfano := messageChannel.fano_uniform code.decode
  have hmutual :
      messageChannel.mutualInformation (FiniteDistribution.uniform (Fin code.messageCount)) ≤
        (blocklength : ℝ) * channel.informationCapacityBits * Real.log 2 := by
    rw [show messageChannel.mutualInformation (FiniteDistribution.uniform (Fin code.messageCount)) =
        (channel.block blocklength).mutualInformation
          ((FiniteDistribution.uniform (Fin code.messageCount)).map code.encode) by
      exact (channel.block blocklength).encoded_mutualInformation code.encode
        (FiniteDistribution.uniform (Fin code.messageCount))]
    exact channel.block_mutualInformation_le_informationCapacityBits_mul_log_two
      blocklength ((FiniteDistribution.uniform (Fin code.messageCount)).map code.encode)
  have herror :
      (identityEncoderCode messageChannel code.decode).averageErrorProbability =
        code.averageErrorProbability := by
    simp [identityEncoderCode, messageChannel, encoded, BlockCode.averageErrorProbability,
      BlockCode.toOneShotCode, OneShotCode.averageErrorProbability,
      OneShotCode.averageSuccessProbability, OneShotCode.successProbability]
  rw [herror] at hfano
  simpa using (show
    Real.log (Fintype.card (Fin code.messageCount)) ≤
      (blocklength : ℝ) * channel.informationCapacityBits * Real.log 2 + Real.log 2 +
        code.averageErrorProbability * Real.log (Fintype.card (Fin code.messageCount)) by
    linarith)

/-- Every positive-blocklength code obeys a Fano rate bound. -/
@[capacity_shared_api]
theorem blockCode_rate_bound
    (channel : FiniteChannel X Y) {blocklength : ℕ}
    (code : BlockCode channel blocklength) (hblocklength : 0 < blocklength) :
    (1 - code.averageErrorProbability) * code.rate ≤
      channel.informationCapacityBits + (blocklength : ℝ)⁻¹ := by
  have hlogBound := channel.blockCode_log_messageCount_le code
  have hblocklengthReal : 0 < (blocklength : ℝ) := by exact_mod_cast hblocklength
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hrearranged :
      (1 - code.averageErrorProbability) * Real.log code.messageCount ≤
        (blocklength : ℝ) * channel.informationCapacityBits * Real.log 2 + Real.log 2 := by
    linarith
  unfold BlockCode.rate Real.logb
  calc
    (1 - code.averageErrorProbability) *
        (Real.log code.messageCount / Real.log 2 / (blocklength : ℝ)) =
        ((1 - code.averageErrorProbability) * Real.log code.messageCount) /
          ((blocklength : ℝ) * Real.log 2) := by
      field_simp [hblocklengthReal.ne', hlogTwo.ne']
    _ ≤ ((blocklength : ℝ) * channel.informationCapacityBits * Real.log 2 +
          Real.log 2) / ((blocklength : ℝ) * Real.log 2) :=
      div_le_div_of_nonneg_right hrearranged
        (mul_pos hblocklengthReal hlogTwo).le
    _ = channel.informationCapacityBits + (blocklength : ℝ)⁻¹ := by
      field_simp [hblocklengthReal.ne', hlogTwo.ne']

namespace AchievableRate

/-- No achievable finite-channel rate exceeds single-letter information capacity. -/
@[capacity_shared_api]
theorem le_informationCapacityBits [Nonempty X]
    (channel : FiniteChannel X Y) {rate : ℝ}
    (hachievable : channel.AchievableRate rate) :
    rate ≤ channel.informationCapacityBits := by
  by_contra hrateCapacity
  have hstrict : channel.informationCapacityBits < rate := lt_of_not_ge hrateCapacity
  have hcapacityNonnegative := channel.informationCapacityBits_nonnegative
  have hratePositive : 0 < rate := lt_of_le_of_lt hcapacityNonnegative hstrict
  let gap := rate - channel.informationCapacityBits
  have hgap : 0 < gap := by
    dsimp [gap]
    linarith
  have hgapRate : gap ≤ rate := by
    dsimp [gap]
    linarith
  let ε := gap / (4 * rate)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hεlt : ε < 1 := by
    apply (div_lt_one (mul_pos (by norm_num) hratePositive)).2
    linarith
  have hεRate : ε * rate = gap / 4 := by
    dsimp [ε]
    field_simp [hratePositive.ne']
  obtain ⟨firstBlocklength, hfirstPositive, hcodes⟩ := hachievable ε hε
  obtain ⟨blocklength, hblocklengthLarge⟩ :=
    exists_nat_gt (max (firstBlocklength : ℝ) (4 / gap))
  have hfirstBlocklength : firstBlocklength ≤ blocklength := by
    exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hblocklengthLarge).le
  have hblocklengthPositive : 0 < blocklength :=
    lt_of_lt_of_le hfirstPositive hfirstBlocklength
  have hblocklengthReal : 0 < (blocklength : ℝ) := by
    exact_mod_cast hblocklengthPositive
  have hfourDiv : 4 / gap < (blocklength : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hblocklengthLarge
  have hfourProduct : 4 < (blocklength : ℝ) * gap :=
    (div_lt_iff₀ hgap).mp hfourDiv
  have hinversePositive : 0 < (blocklength : ℝ)⁻¹ := inv_pos.mpr hblocklengthReal
  have hinverseProduct : (blocklength : ℝ) * (blocklength : ℝ)⁻¹ = 1 :=
    mul_inv_cancel₀ hblocklengthReal.ne'
  have hinverseSmall : (blocklength : ℝ)⁻¹ < gap / 4 := by
    nlinarith
  obtain ⟨code, herror, hcodeRate⟩ := hcodes blocklength hfirstBlocklength
  have hfactorNonnegative : 0 ≤ 1 - code.averageErrorProbability := by
    linarith
  have hlower :
      (1 - ε) * rate ≤ (1 - code.averageErrorProbability) * code.rate := by
    calc
      (1 - ε) * rate ≤ (1 - code.averageErrorProbability) * rate := by
        exact mul_le_mul_of_nonneg_right (by linarith) hratePositive.le
      _ ≤ (1 - code.averageErrorProbability) * code.rate :=
        mul_le_mul_of_nonneg_left hcodeRate hfactorNonnegative
  have hupper := channel.blockCode_rate_bound code hblocklengthPositive
  have hcombined :
      (1 - ε) * rate ≤
        channel.informationCapacityBits + (blocklength : ℝ)⁻¹ :=
    hlower.trans hupper
  dsimp [gap] at hgap hεRate hinverseSmall
  nlinarith

end AchievableRate

/-- Every finite channel satisfies the pointwise operational converse. -/
@[capacity_shared_api]
theorem hasAchievableRateConverse
    (channel : FiniteChannel X Y) : channel.HasAchievableRateConverse := by
  intro rate hrate
  classical
  cases isEmpty_or_nonempty X with
  | inl hX =>
      letI : IsEmpty X := hX
      exact (channel.not_achievableRate_of_isEmpty rate hrate).elim
  | inr hX =>
      letI : Nonempty X := hX
      exact hrate.le_informationCapacityBits channel

/-- The coding theorem for a finite channel with nonempty input alphabet. -/
@[capacity_shared_api]
theorem codingTheorem [Nonempty X]
    (channel : FiniteChannel X Y) : channel.SatisfiesCodingTheorem :=
  channel.satisfiesCodingTheorem_of_randomCodingBounds_converse
    channel.hasRandomCodingBounds channel.hasAchievableRateConverse

/-- The finite-channel coding theorem, including the empty-input convention. -/
@[capacity_shared_api]
theorem codingTheorem_all
    (channel : FiniteChannel X Y) : channel.SatisfiesCodingTheorem :=
  channel.finiteDMCSatisfiesCodingTheorem_of_bounds
    channel.hasRandomCodingBounds channel.hasAchievableRateConverse

end FiniteChannel

end CapacityAtlas
