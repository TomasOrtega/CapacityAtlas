/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
Source: https://github.com/TomasOrtega/CapacityAtlasCausalState/blob/0176a0e9fed6ec13fd2f566d9906c3ea8103d1cc/CapacityAtlasCausal/Converse.lean
Reuses shared Fano normalization and the vanishing-error rate converse.
-/

import CapacityAtlasForMathlib.InformationTheory.CausalState.BlockInformation
import CapacityAtlasForMathlib.InformationTheory.CodingConverse
import CapacityAtlasForMathlib.InformationTheory.FiniteChannelOptimization

open scoped BigOperators
open CapacityAtlas

namespace CapacityAtlasCausal

attribute [local instance] Classical.propDecidable

variable {X S Y : Type*} [Fintype X] [Fintype S] [Fintype Y] [Nonempty X]

/-- Fano bounds the message count for every deterministic causal code. -/
theorem blockCode_log_messageCount_le (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) {blocklength : ℕ}
    (code : CausalState.BlockCode state channels blocklength) :
    Real.log code.messageCount ≤
      (blocklength : ℝ) * (CausalState.strategyChannel state channels).informationCapacityBits *
        Real.log 2 + Real.log 2 +
          code.averageErrorProbability * Real.log code.messageCount := by
  letI : Nonempty (Fin code.messageCount) := Fin.pos_iff_nonempty.mp code.messageCount_pos
  let messageChannel := (CausalState.blockChannel state channels blocklength).encoded code.encode
  have hfano := messageChannel.fano_uniform code.decode
  change Real.log (Fintype.card (Fin code.messageCount)) ≤
    messageChannel.mutualInformation (FiniteDistribution.uniform (Fin code.messageCount)) +
      Real.log 2 + code.averageErrorProbability *
        Real.log (Fintype.card (Fin code.messageCount)) at hfano
  have hmutual := block_mutualInformation_le state channels blocklength code.encode
    (FiniteDistribution.uniform (Fin code.messageCount))
  simp only [Fintype.card_fin] at hfano
  dsimp [messageChannel] at hfano
  linarith

/-- The rate bound is normalized per physical channel use. -/
theorem blockCode_rate_bound (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) {blocklength : ℕ}
    (code : CausalState.BlockCode state channels blocklength) (hblocklength : 0 < blocklength) :
    (1 - code.averageErrorProbability) * code.rate ≤
      (CausalState.strategyChannel state channels).informationCapacityBits +
        (blocklength : ℝ)⁻¹ := by
  exact fano_rate_bound hblocklength (blockCode_log_messageCount_le state channels code)

/-- Past state dependence cannot increase the achievable rate beyond strategy capacity. -/
theorem achievableRate_le_strategyCapacity (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) {rate : ℝ}
    (hachievable : CausalState.AchievableRate state channels rate) :
    rate ≤ (CausalState.strategyChannel state channels).informationCapacityBits := by
  apply rate_le_of_fano_bounds
    (CausalState.strategyChannel state channels).informationCapacityBits_nonnegative
  intro hrate ε hε hεlt
  obtain ⟨firstBlocklength, hfirstPositive, hcodes⟩ := hachievable ε hε
  filter_upwards [Filter.eventually_ge_atTop firstBlocklength] with n hn
  obtain ⟨code, herror, hcodeRate⟩ := hcodes n hn
  exact fano_rate_bound_of_error_le hrate hεlt herror hcodeRate
    (blockCode_rate_bound state channels code (lt_of_lt_of_le hfirstPositive hn))

/-- Shannon strategy coding and the causal converse identify operational capacity. -/
theorem causalStateCapacity (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) :
    CausalState.operationalCapacityBits state channels =
      (CausalState.strategyChannel state channels).informationCapacityBits := by
  let strategy := CausalState.strategyChannel state channels
  have hzero : CausalState.AchievableRate state channels 0 :=
    CausalState.achievableRate_of_strategyChannel (strategy.achievableRate_of_nonpos le_rfl)
  have hbounded : BddAbove {rate | CausalState.AchievableRate state channels rate} :=
    ⟨strategy.informationCapacityBits, fun _ hrate ↦
      achievableRate_le_strategyCapacity state channels hrate⟩
  unfold CausalState.operationalCapacityBits
  apply le_antisymm
  · exact csSup_le ⟨0, hzero⟩ (fun _ hrate ↦
      achievableRate_le_strategyCapacity state channels hrate)
  · apply le_of_forall_lt_imp_le_of_dense
    intro rate hrate
    exact le_csSup hbounded (CausalState.achievableRate_of_strategyChannel
      (strategy.achievableRate_of_lt_informationCapacityBits hrate))

/-- The finite strategy alphabet admits an input attaining causal operational capacity. -/
theorem exists_capacityAchieving_strategy (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) :
    ∃ input : FiniteDistribution (S → X),
      (CausalState.strategyChannel state channels).mutualInformationBits input =
        CausalState.operationalCapacityBits state channels := by
  rw [causalStateCapacity state channels]
  exact (CausalState.strategyChannel state channels).exists_capacityAchieving_input

end CapacityAtlasCausal
