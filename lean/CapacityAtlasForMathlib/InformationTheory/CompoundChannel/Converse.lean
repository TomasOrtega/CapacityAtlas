/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
Source: https://github.com/TomasOrtega/CapacityAtlasCompound/blob/1d5cbdc0a8cfb5d034facdb8d1e2473bb3c40ebe/CapacityAtlasCompound/Converse.lean
Reuses shared Fano normalization and the vanishing-error rate converse.
-/

import CapacityAtlasForMathlib.InformationTheory.CompoundChannel
import CapacityAtlasForMathlib.InformationTheory.BlockInputInformation
import CapacityAtlasForMathlib.InformationTheory.CodingConverse

open scoped BigOperators
open CapacityAtlas

namespace CapacityAtlasCompound

variable {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S]

/-- The encoder's word distribution is independent of the channel member. -/
noncomputable def blockCodeInputDistribution {n : ℕ}
    (code : CompoundChannel.BlockCode X Y n) : FiniteDistribution (Fin n → X) := by
  classical
  letI : Nonempty (Fin code.messageCount) := Fin.pos_iff_nonempty.mp code.messageCount_pos
  exact (FiniteDistribution.uniform (Fin code.messageCount)).map code.encode

/-- Uniform averaging of the same input marginals for every channel member. -/
noncomputable def blockCodeAverageInput {n : ℕ}
    (code : CompoundChannel.BlockCode X Y n) (hn : 0 < n) : FiniteDistribution X := by
  letI : NeZero n := ⟨hn.ne'⟩
  exact (blockCodeInputDistribution code).averageCoordinateMarginal

/-- Fano's inequality retains the common averaged input distribution. -/
theorem blockCode_log_messageCount_le (channel : FiniteChannel X Y) {n : ℕ}
    (code : CompoundChannel.BlockCode X Y n) (hn : 0 < n) :
    Real.log code.messageCount ≤
      (n : ℝ) * channel.mutualInformation (blockCodeAverageInput code hn) + Real.log 2 +
        code.averageErrorProbability channel * Real.log code.messageCount := by
  classical
  letI : Nonempty (Fin code.messageCount) := Fin.pos_iff_nonempty.mp code.messageCount_pos
  letI : NeZero n := ⟨hn.ne'⟩
  have hfano := ((channel.block n).encoded code.encode).fano_uniform code.decode
  simp only [Fintype.card_fin] at hfano
  change Real.log code.messageCount ≤
    ((channel.block n).encoded code.encode).mutualInformation
      (FiniteDistribution.uniform (Fin code.messageCount)) + Real.log 2 +
        code.averageErrorProbability channel * Real.log code.messageCount at hfano
  rw [FiniteChannel.encoded_mutualInformation] at hfano
  have hmutual :=
    channel.block_mutualInformation_le_mul_averageCoordinateMarginal
      (blockCodeInputDistribution code)
  change (channel.block n).mutualInformation
      ((FiniteDistribution.uniform (Fin code.messageCount)).map code.encode) ≤
    (n : ℝ) * channel.mutualInformation (blockCodeAverageInput code hn) at hmutual
  linarith

/-- A statewise rate bound with an input law shared by the whole family. -/
theorem blockCode_rate_bound (channel : FiniteChannel X Y) {n : ℕ}
    (code : CompoundChannel.BlockCode X Y n) (hn : 0 < n) :
    (1 - code.averageErrorProbability channel) * code.rate ≤
      channel.mutualInformationBits (blockCodeAverageInput code hn) + (n : ℝ)⁻¹ := by
  apply fano_rate_bound hn
  have hlogTwo : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  simpa only [FiniteChannel.mutualInformationBits, mul_assoc, div_mul_cancel₀ _ hlogTwo] using
    blockCode_log_messageCount_le channel code hn

/-- Uniform reliability allows minimization over the family with the same input law. -/
theorem blockCode_uniform_rate_bound [Nonempty S]
    (channels : S → FiniteChannel X Y) {n : ℕ}
    (code : CompoundChannel.BlockCode X Y n) (hn : 0 < n)
    {rate ε : ℝ} (hrate : 0 ≤ rate) (hε : ε < 1)
    (herror : ∀ s, code.averageErrorProbability (channels s) ≤ ε)
    (hcodeRate : rate ≤ code.rate) :
    (1 - ε) * rate ≤ CompoundChannel.informationCapacityBits channels + (n : ℝ)⁻¹ := by
  have hcommon : (1 - ε) * rate - (n : ℝ)⁻¹ ≤
      CompoundChannel.worstInformationBits channels (blockCodeAverageInput code hn) := by
    apply CompoundChannel.le_worstInformationBits
    intro s
    have hcombined := fano_rate_bound_of_error_le hrate hε (herror s) hcodeRate
      (blockCode_rate_bound (channels s) code hn)
    linarith
  have hcapacity :=
    CompoundChannel.worstInformationBits_le_informationCapacityBits channels
      (blockCodeAverageInput code hn)
  linarith

/-- No uniformly achievable rate exceeds the max–min information target. -/
theorem achievableRate_le_informationCapacityBits [Nonempty S] [Nonempty X]
    (channels : S → FiniteChannel X Y) {rate : ℝ}
    (hachievable : CompoundChannel.AchievableRate channels rate) :
    rate ≤ CompoundChannel.informationCapacityBits channels := by
  apply rate_le_of_fano_bounds (CompoundChannel.informationCapacityBits_nonnegative channels)
  intro hrate ε hε hεlt
  obtain ⟨firstBlocklength, hfirstPositive, hcodes⟩ := hachievable ε hε
  filter_upwards [Filter.eventually_ge_atTop firstBlocklength] with n hn
  obtain ⟨code, herror, hcodeRate⟩ := hcodes n hn
  exact blockCode_uniform_rate_bound channels code (lt_of_lt_of_le hfirstPositive hn)
    hrate hεlt herror hcodeRate

theorem achievableRates_bddAbove [Nonempty S] [Nonempty X]
    (channels : S → FiniteChannel X Y) :
    BddAbove {rate | rate = 0 ∨ CompoundChannel.AchievableRate channels rate} := by
  refine ⟨CompoundChannel.informationCapacityBits channels, ?_⟩
  rintro rate (rfl | hrate)
  · exact CompoundChannel.informationCapacityBits_nonnegative channels
  · exact achievableRate_le_informationCapacityBits channels hrate

/-- The converse for the operational supremum, including its explicit zero rate. -/
theorem operationalCapacityBits_le_informationCapacityBits [Nonempty S] [Nonempty X]
    (channels : S → FiniteChannel X Y) :
    CompoundChannel.operationalCapacityBits channels ≤
      CompoundChannel.informationCapacityBits channels := by
  apply csSup_le
  · exact ⟨0, Or.inl rfl⟩
  · rintro rate (rfl | hrate)
    · exact CompoundChannel.informationCapacityBits_nonnegative channels
    · exact achievableRate_le_informationCapacityBits channels hrate

end CapacityAtlasCompound
