/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.InformationDensity
import CapacityAtlasForMathlib.InformationTheory.OperationalCapacity

open scoped BigOperators

namespace CapacityAtlas

namespace FiniteChannel

variable {A B : Type*} [Fintype A] [Fintype B]

noncomputable local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

private theorem sum_comm_three {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (f : I → J → K → ℝ) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ i, ∑ j, f i j k := by
  calc
    ∑ i, ∑ j, ∑ k, f i j k = ∑ i, ∑ k, ∑ j, f i j k := by
      apply Fintype.sum_congr
      intro i
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, f i j k := by rw [Finset.sum_comm]

/-- The likelihood-ratio threshold test used by the random-coding decoder. -/
def IsInformationDensityCandidate (channel : FiniteChannel A B)
    (input : FiniteDistribution A) (threshold : ℝ) (symbol : A) (output : B) : Prop :=
  0 < channel.transition symbol output ∧
    threshold < channel.informationDensity input (symbol, output)

noncomputable def thresholdDecoder {M : Type*} [Fintype M] [Nonempty M]
    (channel : FiniteChannel A B) (input : FiniteDistribution A) (threshold : ℝ)
    (codebook : M → A) (output : B) : M :=
  if h : ∃ message, channel.IsInformationDensityCandidate input threshold
      (codebook message) output then
    Classical.choose h
  else
    Classical.choice inferInstance

private theorem thresholdDecoder_isCandidate {M : Type*} [Fintype M] [Nonempty M]
    (channel : FiniteChannel A B) (input : FiniteDistribution A) (threshold : ℝ)
    (codebook : M → A) (output : B)
    (hexists : ∃ message, channel.IsInformationDensityCandidate input threshold
      (codebook message) output) :
    channel.IsInformationDensityCandidate input threshold
      (codebook (thresholdDecoder channel input threshold codebook output)) output := by
  rw [thresholdDecoder, dif_pos hexists]
  exact Classical.choose_spec hexists

/-- The threshold decoder associated with a deterministic codebook. -/
noncomputable def thresholdCode {M : Type*} [Fintype M] [Nonempty M]
    (channel : FiniteChannel A B) (input : FiniteDistribution A) (threshold : ℝ)
    (codebook : M → A) : OneShotCode channel M where
  encode := codebook
  decode := thresholdDecoder channel input threshold codebook

private theorem thresholdDecoder_eq_of_unique_candidate
    {M : Type*} [Fintype M] [Nonempty M]
    (channel : FiniteChannel A B) (input : FiniteDistribution A) (threshold : ℝ)
    (codebook : M → A) (output : B) (message : M)
    (hcandidate : channel.IsInformationDensityCandidate input threshold
      (codebook message) output)
    (hother : ∀ other, other ≠ message →
      ¬channel.IsInformationDensityCandidate input threshold (codebook other) output) :
    thresholdDecoder channel input threshold codebook output = message := by
  have hexists : ∃ candidate, channel.IsInformationDensityCandidate input threshold
      (codebook candidate) output := ⟨message, hcandidate⟩
  have hdecoded := thresholdDecoder_isCandidate channel input threshold codebook output hexists
  by_contra hne
  exact hother _ hne hdecoded

private theorem thresholdCode_errorSummand_le
    {M : Type*} [Fintype M] [Nonempty M] [DecidableEq M]
    (channel : FiniteChannel A B) (input : FiniteDistribution A) (threshold : ℝ)
    (codebook : M → A) (message : M) (output : B) :
    (if (thresholdCode channel input threshold codebook).decode output ≠ message then
        channel.transition (codebook message) output
      else 0) ≤
      (if channel.informationDensity input (codebook message, output) ≤ threshold then
          channel.transition (codebook message) output
        else 0) +
        ∑ other : M,
          if other ≠ message ∧
              channel.IsInformationDensityCandidate input threshold (codebook other) output then
            channel.transition (codebook message) output
          else 0 := by
  classical
  let transition := channel.transition (codebook message) output
  have htransition : 0 ≤ transition := channel.nonnegative _ _
  have hsumNonnegative :
      0 ≤ ∑ other : M,
        if other ≠ message ∧
            channel.IsInformationDensityCandidate input threshold (codebook other) output then
          transition
        else 0 := by
    apply Finset.sum_nonneg
    intro other _
    by_cases hother : other ≠ message ∧
        channel.IsInformationDensityCandidate input threshold (codebook other) output
    · simp [hother, htransition]
    · simp [hother]
  by_cases hdecode :
      (thresholdCode channel input threshold codebook).decode output = message
  · rw [if_neg (not_not_intro hdecode)]
    exact add_nonneg (by split_ifs <;> positivity) hsumNonnegative
  rw [if_pos hdecode]
  by_cases hcandidate : channel.IsInformationDensityCandidate input threshold
      (codebook message) output
  · have hdecodedCandidate : channel.IsInformationDensityCandidate input threshold
        (codebook ((thresholdCode channel input threshold codebook).decode output)) output :=
      thresholdDecoder_isCandidate channel input threshold codebook output ⟨message, hcandidate⟩
    have hterm :
        transition ≤
          ∑ other : M,
            if other ≠ message ∧
                channel.IsInformationDensityCandidate input threshold (codebook other) output then
              transition
            else 0 := by
      calc
        transition =
            (if (thresholdCode channel input threshold codebook).decode output ≠ message ∧
                channel.IsInformationDensityCandidate input threshold
                  (codebook ((thresholdCode channel input threshold codebook).decode output))
                  output then transition else 0) := by
              simp [hdecode, hdecodedCandidate]
        _ ≤ ∑ other : M,
            if other ≠ message ∧
                channel.IsInformationDensityCandidate input threshold (codebook other) output then
              transition
            else 0 :=
          Finset.single_le_sum
            (f := fun other : M ↦
              if other ≠ message ∧
                  channel.IsInformationDensityCandidate input threshold (codebook other) output then
                transition
              else 0)
            (fun other _ ↦ by
              by_cases hother : other ≠ message ∧
                  channel.IsInformationDensityCandidate input threshold (codebook other) output
              · simp [hother, htransition]
              · simp [hother])
            (Finset.mem_univ ((thresholdCode channel input threshold codebook).decode output))
    exact hterm.trans (le_add_of_nonneg_left (by split_ifs <;> positivity))
  · by_cases hzero : transition = 0
    · have htransitionZero : channel.transition (codebook message) output = 0 := hzero
      simp [htransitionZero]
    · have hpositive : 0 < transition := lt_of_le_of_ne htransition (Ne.symm hzero)
      have hdensity :
          channel.informationDensity input (codebook message, output) ≤ threshold := by
        exact not_lt.mp (fun hlt ↦ hcandidate ⟨hpositive, hlt⟩)
      rw [if_pos hdensity]
      exact le_add_of_nonneg_right hsumNonnegative

private theorem outputDistribution_le_exp_neg_mul_transition_of_candidate
    (channel : FiniteChannel A B) (input : FiniteDistribution A) (threshold : ℝ)
    (symbol : A) (output : B)
    (hcandidate : channel.IsInformationDensityCandidate input threshold symbol output) :
    channel.outputDistribution input output ≤
      Real.exp (-threshold) * channel.transition symbol output := by
  rcases hcandidate with ⟨htransition, hdensity⟩
  by_cases houtputZero : channel.outputDistribution input output = 0
  · rw [houtputZero]
    exact mul_nonneg (Real.exp_pos _).le (channel.nonnegative symbol output)
  have houtput : 0 < channel.outputDistribution input output :=
    lt_of_le_of_ne ((channel.outputDistribution input).nonnegative output) (Ne.symm houtputZero)
  have hratio :
      0 < channel.transition symbol output / channel.outputDistribution input output :=
    div_pos htransition houtput
  have hexponential :
      Real.exp threshold <
        channel.transition symbol output / channel.outputDistribution input output := by
    rw [← Real.exp_log hratio]
    exact Real.exp_lt_exp.mpr hdensity
  have hscaled :
      Real.exp threshold * channel.outputDistribution input output <
        channel.transition symbol output :=
    (lt_div_iff₀ houtput).mp hexponential
  calc
    channel.outputDistribution input output =
        Real.exp (-threshold) *
          (Real.exp threshold * channel.outputDistribution input output) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp (-threshold) * channel.transition symbol output :=
      mul_le_mul_of_nonneg_left hscaled.le (Real.exp_pos _).le

/-- The output-distribution mass of a false threshold crossing is exponentially small. -/
theorem falseAlarmMass_le_exp_neg
    (channel : FiniteChannel A B) (input : FiniteDistribution A) (threshold : ℝ) :
    (∑ output : B, channel.outputDistribution input output *
      ∑ symbol : A, input symbol *
        if channel.IsInformationDensityCandidate input threshold symbol output then 1 else 0) ≤
      Real.exp (-threshold) := by
  simp_rw [Finset.mul_sum]
  calc
    ∑ output : B, ∑ symbol : A,
        channel.outputDistribution input output *
          (input symbol *
            if channel.IsInformationDensityCandidate input threshold symbol output then 1 else 0) ≤
        ∑ output : B, ∑ symbol : A,
          Real.exp (-threshold) *
            (input symbol * channel.transition symbol output) := by
      apply Finset.sum_le_sum
      intro output _
      apply Finset.sum_le_sum
      intro symbol _
      by_cases hcandidate :
          channel.IsInformationDensityCandidate input threshold symbol output
      · rw [if_pos hcandidate, mul_one]
        calc
          channel.outputDistribution input output * input symbol =
              input symbol * channel.outputDistribution input output := by ring
          _ ≤ input symbol *
                (Real.exp (-threshold) * channel.transition symbol output) :=
            mul_le_mul_of_nonneg_left
              (outputDistribution_le_exp_neg_mul_transition_of_candidate
                channel input threshold symbol output hcandidate)
              (input.nonnegative symbol)
          _ = Real.exp (-threshold) *
                (input symbol * channel.transition symbol output) := by ring
      · have hright :
            0 ≤ Real.exp (-threshold) *
              (input symbol * channel.transition symbol output) :=
          mul_nonneg (Real.exp_pos _).le
            (mul_nonneg (input.nonnegative symbol) (channel.nonnegative symbol output))
        simpa [hcandidate] using hright
    _ = Real.exp (-threshold) *
        ∑ symbol : A, input symbol * ∑ output : B, channel.transition symbol output := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Fintype.sum_congr
      intro symbol
      rw [Finset.mul_sum]
      rw [Finset.mul_sum]
    _ = Real.exp (-threshold) := by simp

/-- Joint mass below an information-density threshold. -/
noncomputable def informationDensityLowerTailMass
    (channel : FiniteChannel A B) (input : FiniteDistribution A) (threshold : ℝ) : ℝ :=
  ∑ output : B, ∑ symbol : A,
    if channel.informationDensity input (symbol, output) ≤ threshold then
      channel.jointMass input (symbol, output)
    else 0

private theorem sum_codebookMass_mul_miss
    {M : Type*} [Fintype M] [Nonempty M] [DecidableEq M]
    (channel : FiniteChannel A B) (input : FiniteDistribution A) (threshold : ℝ)
    (message : M) (output : B) :
    (∑ codebook : M → A, FiniteProductProbability.mass input codebook *
      if channel.informationDensity input (codebook message, output) ≤ threshold then
        channel.transition (codebook message) output
      else 0) =
      ∑ symbol : A, input symbol *
        if channel.informationDensity input (symbol, output) ≤ threshold then
          channel.transition symbol output
        else 0 := by
  let miss : A → ℝ := fun symbol ↦
    if channel.informationDensity input (symbol, output) ≤ threshold then
      channel.transition symbol output
    else 0
  simpa only [miss, FiniteProductProbability.mean] using
    (FiniteProductProbability.sum_mass_mul_apply
      (ι := M) input miss input.sum_probability message)

private theorem sum_codebookMass_mul_falseCandidate
    {M : Type*} [Fintype M] [Nonempty M] [DecidableEq M]
    (channel : FiniteChannel A B) (input : FiniteDistribution A) (threshold : ℝ)
    (message other : M) (hne : message ≠ other) (output : B) :
    (∑ codebook : M → A, FiniteProductProbability.mass input codebook *
      (if channel.IsInformationDensityCandidate input threshold (codebook other) output then
        channel.transition (codebook message) output
      else 0)) =
      channel.outputDistribution input output *
        ∑ symbol : A, input symbol *
          if channel.IsInformationDensityCandidate input threshold symbol output then 1 else 0 := by
  let sent : A → ℝ := fun symbol ↦ channel.transition symbol output
  let candidate : A → ℝ := fun symbol ↦
    if channel.IsInformationDensityCandidate input threshold symbol output then 1 else 0
  calc
    ∑ codebook : M → A, FiniteProductProbability.mass input codebook *
        (if channel.IsInformationDensityCandidate input threshold (codebook other) output then
          channel.transition (codebook message) output
        else 0) =
        ∑ codebook : M → A, FiniteProductProbability.mass input codebook *
          (sent (codebook message) * candidate (codebook other)) := by
      apply Fintype.sum_congr
      intro codebook
      by_cases hcandidate : channel.IsInformationDensityCandidate input threshold
          (codebook other) output <;> simp [sent, candidate, hcandidate]
    _ = FiniteProductProbability.mean input sent *
        FiniteProductProbability.mean input candidate :=
      FiniteProductProbability.sum_mass_mul_apply_mul_apply
        input sent candidate input.sum_probability hne
    _ = channel.outputDistribution input output *
        ∑ symbol : A, input symbol *
          if channel.IsInformationDensityCandidate input threshold symbol output then 1 else 0 := by
      unfold FiniteProductProbability.mean sent candidate
      rfl

private theorem expected_thresholdCode_errorProbability_le
    {M : Type*} [Fintype M] [Nonempty M] [DecidableEq M]
    (channel : FiniteChannel A B) (input : FiniteDistribution A) (threshold : ℝ)
    (message : M) :
    (∑ codebook : M → A, FiniteProductProbability.mass input codebook *
      (thresholdCode channel input threshold codebook).errorProbability message) ≤
      channel.informationDensityLowerTailMass input threshold +
        (Fintype.card M : ℝ) * Real.exp (-threshold) := by
  simp_rw [OneShotCode.errorProbability_eq_sum_decode_ne]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    ∑ output : B, ∑ codebook : M → A,
        FiniteProductProbability.mass input codebook *
          (if (thresholdCode channel input threshold codebook).decode output ≠ message then
            channel.transition (codebook message) output
          else 0) ≤
        ∑ output : B, ∑ codebook : M → A,
          FiniteProductProbability.mass input codebook *
            ((if channel.informationDensity input (codebook message, output) ≤ threshold then
                channel.transition (codebook message) output
              else 0) +
              ∑ other : M,
                if other ≠ message ∧
                    channel.IsInformationDensityCandidate input threshold
                      (codebook other) output then
                  channel.transition (codebook message) output
                else 0) := by
      apply Finset.sum_le_sum
      intro output _
      apply Finset.sum_le_sum
      intro codebook _
      exact mul_le_mul_of_nonneg_left
        (thresholdCode_errorSummand_le channel input threshold codebook message output)
        (FiniteProductProbability.mass_nonnegative input input.nonnegative codebook)
    _ = channel.informationDensityLowerTailMass input threshold +
        ∑ other : M,
          ∑ output : B, channel.outputDistribution input output *
            ∑ symbol : A, input symbol *
              if other ≠ message ∧
                  channel.IsInformationDensityCandidate input threshold symbol output then 1 else 0 := by
      simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · unfold informationDensityLowerTailMass jointMass
        apply Fintype.sum_congr
        intro output
        rw [sum_codebookMass_mul_miss channel input threshold message output]
        apply Fintype.sum_congr
        intro symbol
        split_ifs <;> ring
      · rw [sum_comm_three]
        apply Fintype.sum_congr
        intro other
        apply Fintype.sum_congr
        intro output
        by_cases hne : other ≠ message
        · calc
            ∑ codebook : M → A, FiniteProductProbability.mass input codebook *
                (if other ≠ message ∧
                    channel.IsInformationDensityCandidate input threshold
                      (codebook other) output then
                  channel.transition (codebook message) output
                else 0) =
                ∑ codebook : M → A, FiniteProductProbability.mass input codebook *
                  (if channel.IsInformationDensityCandidate input threshold
                      (codebook other) output then
                    channel.transition (codebook message) output
                  else 0) := by simp [hne]
            _ = channel.outputDistribution input output *
                ∑ symbol : A, input symbol *
                  if channel.IsInformationDensityCandidate input threshold symbol output then
                    1
                  else 0 :=
              sum_codebookMass_mul_falseCandidate channel input threshold
                message other (Ne.symm hne) output
            _ = channel.outputDistribution input output *
                ∑ symbol : A, input symbol *
                  if other ≠ message ∧
                      channel.IsInformationDensityCandidate input threshold symbol output then
                    1
                  else 0 := by simp [hne]
            _ = ∑ symbol : A, channel.outputDistribution input output *
                (input symbol *
                  if other ≠ message ∧
                      channel.IsInformationDensityCandidate input threshold symbol output then
                    1
                  else 0) := by rw [Finset.mul_sum]
        · simp [hne]
    _ ≤ channel.informationDensityLowerTailMass input threshold +
        ∑ _other : M, Real.exp (-threshold) := by
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro other _
      by_cases hne : other ≠ message
      · simpa [hne] using channel.falseAlarmMass_le_exp_neg input threshold
      · simp [hne, (Real.exp_pos (-threshold)).le]
    _ = channel.informationDensityLowerTailMass input threshold +
        (Fintype.card M : ℝ) * Real.exp (-threshold) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- A one-shot threshold random-coding bound with a deterministic selected codebook. -/
@[capacity_shared_api]
theorem exists_oneShotCode_averageErrorProbability_le
    {M : Type*} [Fintype M] [Nonempty M] [DecidableEq M]
    (channel : FiniteChannel A B) (input : FiniteDistribution A) (threshold : ℝ) :
    ∃ code : OneShotCode channel M,
      code.averageErrorProbability ≤
        channel.informationDensityLowerTailMass input threshold +
          (Fintype.card M : ℝ) * Real.exp (-threshold) := by
  letI : Nonempty A := input.nonempty
  let codeOf : (M → A) → OneShotCode channel M :=
    thresholdCode channel input threshold
  let bound := channel.informationDensityLowerTailMass input threshold +
    (Fintype.card M : ℝ) * Real.exp (-threshold)
  have hensemble :
      (∑ codebook : M → A, FiniteProductProbability.mass input codebook *
        (codeOf codebook).averageErrorProbability) ≤ bound := by
    have hcardNonnegative : 0 ≤ (Fintype.card M : ℝ)⁻¹ := by positivity
    calc
      ∑ codebook : M → A, FiniteProductProbability.mass input codebook *
          (codeOf codebook).averageErrorProbability =
          (Fintype.card M : ℝ)⁻¹ *
            ∑ message : M, ∑ codebook : M → A,
              FiniteProductProbability.mass input codebook *
                (codeOf codebook).errorProbability message := by
        simp_rw [OneShotCode.averageErrorProbability_eq, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Fintype.sum_congr
        intro message
        apply Fintype.sum_congr
        intro codebook
        ring
      _ ≤ (Fintype.card M : ℝ)⁻¹ * ∑ _message : M, bound := by
        apply mul_le_mul_of_nonneg_left _ hcardNonnegative
        apply Finset.sum_le_sum
        intro message _
        exact expected_thresholdCode_errorProbability_le
          channel input threshold message
      _ = bound := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hcard : (Fintype.card M : ℝ) ≠ 0 := by
          exact_mod_cast Fintype.card_ne_zero
        field_simp
  obtain ⟨codebook, hcodebook⟩ :=
    FiniteProductProbability.exists_value_le_weighted_mean
      (FiniteProductProbability.mass (ι := M) input)
      (fun codebook ↦ (codeOf codebook).averageErrorProbability)
      (FiniteProductProbability.mass_nonnegative input input.nonnegative)
      (FiniteProductProbability.sum_mass input input.sum_probability)
  exact ⟨codeOf codebook, hcodebook.trans hensemble⟩

/-- The block-channel lower tail is the lower tail of the additive coordinate statistic. -/
theorem block_informationDensityLowerTailMass_eq
    {X Y : Type*} [Fintype X] [Fintype Y]
    (channel : FiniteChannel X Y) (input : FiniteDistribution X)
    (n : ℕ) (threshold : ℝ) :
    (channel.block n).informationDensityLowerTailMass (input.iid n) threshold =
      ∑ pairs : Fin n → X × Y,
        if channel.blockInformationDensity input pairs ≤ threshold then
          FiniteProductProbability.mass (channel.jointMass input) pairs
        else 0 := by
  unfold informationDensityLowerTailMass
  rw [Finset.sum_comm]
  calc
    (∑ inputWord : Fin n → X, ∑ outputWord : Fin n → Y,
        if (channel.block n).informationDensity (input.iid n) (inputWord, outputWord) ≤
            threshold then
          (channel.block n).jointMass (input.iid n) (inputWord, outputWord)
        else 0) =
        (∑ words : (Fin n → X) × (Fin n → Y),
          if (channel.block n).informationDensity (input.iid n) words ≤ threshold then
            (channel.block n).jointMass (input.iid n) words
          else 0) := by rw [Fintype.sum_prod_type]
    _ = (∑ pairs : Fin n → X × Y,
        if channel.blockInformationDensity input pairs ≤ threshold then
          FiniteProductProbability.mass (channel.jointMass input) pairs
        else 0) := by
      apply Fintype.sum_equiv (wordPairEquiv n)
      intro words
      by_cases hmass : (channel.block n).jointMass (input.iid n) words = 0
      · have hproductMass :
            FiniteProductProbability.mass (channel.jointMass input) (wordPairEquiv n words) =
              0 := by
          rw [← channel.block_jointMass_iid input n words]
          exact hmass
        simp [hmass, hproductMass]
      · rw [channel.block_informationDensity_eq_sum input n words hmass,
          channel.block_jointMass_iid input n words]
        rfl

/-- The finite-block random-coding estimate for a finite memoryless channel. -/
@[capacity_shared_api]
theorem exists_blockCode_averageErrorProbability_le
    {X Y : Type*} [Fintype X] [Fintype Y]
    (channel : FiniteChannel X Y) (input : FiniteDistribution X)
    (δ : ℝ) {blocklength messages : ℕ}
    (hblocklength : 0 < blocklength) (hmessageCount : 0 < messages) (hδ : 0 < δ) :
    ∃ code : BlockCode channel blocklength,
      code.messageCount = messages ∧
        code.averageErrorProbability ≤
          ((blocklength : ℝ) * channel.informationVariance input) /
              (((blocklength : ℝ) * δ) ^ 2) +
            (messages : ℝ) * Real.exp
              (-((blocklength : ℝ) * channel.mutualInformation input -
                (blocklength : ℝ) * δ)) := by
  letI : Nonempty (Fin messages) := Fin.pos_iff_nonempty.mp hmessageCount
  let threshold :=
    (blocklength : ℝ) * channel.mutualInformation input - (blocklength : ℝ) * δ
  obtain ⟨oneShot, honeShot⟩ :=
    (channel.block blocklength).exists_oneShotCode_averageErrorProbability_le
      (input.iid blocklength) threshold (M := Fin messages)
  let code : BlockCode channel blocklength :=
    { messageCount := messages
      messageCount_pos := hmessageCount
      encode := oneShot.encode
      decode := oneShot.decode }
  refine ⟨code, rfl, ?_⟩
  have htail :
      (channel.block blocklength).informationDensityLowerTailMass
          (input.iid blocklength) threshold ≤
        ((blocklength : ℝ) * channel.informationVariance input) /
          (((blocklength : ℝ) * δ) ^ 2) := by
    rw [channel.block_informationDensityLowerTailMass_eq input blocklength threshold]
    exact channel.blockInformationDensity_lowerTail_le
      input hblocklength hδ
  have hselected :
      oneShot.averageErrorProbability ≤
        ((blocklength : ℝ) * channel.informationVariance input) /
            (((blocklength : ℝ) * δ) ^ 2) +
          (messages : ℝ) * Real.exp (-threshold) := by
    simpa using honeShot.trans (add_le_add_left htail _)
  simpa [code, BlockCode.averageErrorProbability, BlockCode.toOneShotCode, threshold] using hselected

/-- Information-density variance supplies the abstract random-coding bound. -/
@[capacity_shared_api]
theorem hasRandomCodingBound
    {X Y : Type*} [Fintype X] [Fintype Y]
    (channel : FiniteChannel X Y) (input : FiniteDistribution X) :
    channel.HasRandomCodingBound input (channel.informationVariance input) := by
  intro δ blocklength messageCount hblocklength hmessageCount hδ
  exact channel.exists_blockCode_averageErrorProbability_le
    input δ hblocklength hmessageCount hδ

/-- Every finite channel has the finite-block estimates required for direct coding. -/
@[capacity_shared_api]
theorem hasRandomCodingBounds
    {X Y : Type*} [Fintype X] [Fintype Y]
    (channel : FiniteChannel X Y) : channel.HasRandomCodingBounds := by
  intro input
  exact ⟨channel.informationVariance input, channel.hasRandomCodingBound input⟩

/-- Every rate below finite-channel information capacity is achievable. -/
@[capacity_shared_api]
theorem achievableRate_of_lt_informationCapacityBits
    {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X]
    (channel : FiniteChannel X Y) {rate : ℝ}
    (hrate : rate < channel.informationCapacityBits) :
    channel.AchievableRate rate :=
  achievableRate_of_lt_informationCapacityBits_of_randomCodingBounds
    channel channel.hasRandomCodingBounds hrate

end FiniteChannel

end CapacityAtlas
