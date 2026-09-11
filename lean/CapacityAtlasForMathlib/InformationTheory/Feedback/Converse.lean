/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
Source: https://github.com/TomasOrtega/CapacityAtlasFeedback/blob/b35299f221ad1c17ccbafb45082c22a5379a99e9/CapacityAtlasFeedback/Converse.lean
Reuses shared Fano normalization and the vanishing-error rate converse.
-/

import CapacityAtlasForMathlib.InformationTheory.Feedback.BlockInformation
import CapacityAtlasForMathlib.InformationTheory.CodingConverse

open scoped BigOperators
open CapacityAtlas

namespace CapacityAtlasFeedback

attribute [local instance] Classical.propDecidable

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Fano bounds the message count for every deterministic feedback code. -/
theorem blockCode_log_messageCount_le (channel : FiniteChannel X Y) {blocklength : ℕ}
    (code : Feedback.BlockCode channel blocklength) :
    Real.log code.messageCount ≤
      (blocklength : ℝ) * channel.informationCapacityBits *
        Real.log 2 + Real.log 2 +
          code.averageErrorProbability * Real.log code.messageCount := by
  letI : Nonempty (Fin code.messageCount) := Fin.pos_iff_nonempty.mp code.messageCount_pos
  let messageChannel := (Feedback.blockChannel channel blocklength).encoded code.encode
  have hfano := messageChannel.fano_uniform code.decode
  change Real.log (Fintype.card (Fin code.messageCount)) ≤
    messageChannel.mutualInformation (FiniteDistribution.uniform (Fin code.messageCount)) +
      Real.log 2 + code.averageErrorProbability *
        Real.log (Fintype.card (Fin code.messageCount)) at hfano
  have hmutual := block_mutualInformation_le channel blocklength code.encode
    (FiniteDistribution.uniform (Fin code.messageCount))
  simp only [Fintype.card_fin] at hfano
  dsimp [messageChannel] at hfano
  linarith

/-- The rate bound is normalized per physical channel use. -/
theorem blockCode_rate_bound (channel : FiniteChannel X Y) {blocklength : ℕ}
    (code : Feedback.BlockCode channel blocklength) (hblocklength : 0 < blocklength) :
    (1 - code.averageErrorProbability) * code.rate ≤
      channel.informationCapacityBits +
        (blocklength : ℝ)⁻¹ := by
  exact fano_rate_bound hblocklength (blockCode_log_messageCount_le channel code)

/-- Strictly causal output feedback cannot raise an achievable rate above channel capacity. -/
theorem achievableRate_le_informationCapacityBits [Nonempty X]
    (channel : FiniteChannel X Y) {rate : ℝ}
    (hachievable : Feedback.AchievableRate channel rate) :
    rate ≤ channel.informationCapacityBits := by
  apply rate_le_of_fano_bounds channel.informationCapacityBits_nonnegative
  intro hrate ε hε hεlt
  obtain ⟨firstBlocklength, hfirstPositive, hcodes⟩ := hachievable ε hε
  filter_upwards [Filter.eventually_ge_atTop firstBlocklength] with n hn
  obtain ⟨code, herror, hcodeRate⟩ := hcodes n hn
  exact fano_rate_bound_of_error_le hrate hεlt herror hcodeRate
    (blockCode_rate_bound channel code (lt_of_lt_of_le hfirstPositive hn))

/-- Every achievable feedback rate has the same finite upper bound. -/
theorem achievableRates_bddAbove [Nonempty X] (channel : FiniteChannel X Y) :
    BddAbove {rate | Feedback.AchievableRate channel rate} :=
  ⟨channel.informationCapacityBits, fun _ hrate ↦
    achievableRate_le_informationCapacityBits channel hrate⟩

/-- The supremum of achievable feedback rates is bounded by ordinary information capacity. -/
theorem operationalCapacityBits_le_informationCapacityBits [Nonempty X]
    (channel : FiniteChannel X Y) :
    Feedback.operationalCapacityBits channel ≤ channel.informationCapacityBits := by
  have hzero : Feedback.AchievableRate channel 0 :=
    Feedback.achievableRate_of_ordinary (channel.achievableRate_of_nonpos le_rfl)
  unfold Feedback.operationalCapacityBits
  exact csSup_le ⟨0, hzero⟩ (fun _ hrate ↦
    achievableRate_le_informationCapacityBits channel hrate)

end CapacityAtlasFeedback
