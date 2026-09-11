/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0

Adapted from TomasOrtega/CapacityAtlasInputCost, commit 5e6a432bc276aa4e08b7f27658daf40e029cda48,
CapacityAtlasCost/Converse.lean. Reuses shared Fano and block-input information bounds.
-/

import CapacityAtlasForMathlib.InformationTheory.InputCost
import CapacityAtlasForMathlib.InformationTheory.CodingConverse
import CapacityAtlasForMathlib.InformationTheory.BlockInputInformation

open scoped BigOperators

namespace CapacityAtlas.FiniteChannel

variable {X Y : Type*} [Fintype X] [Fintype Y]

noncomputable def inputCostPointMass (symbol : X) : FiniteDistribution X := by
  classical
  exact (FiniteDistribution.uniform (Fin 1)).map (fun _ ↦ symbol)

theorem inputCostPointMass_expectedCost (symbol : X) (cost : X → ℝ) :
    (inputCostPointMass symbol).expectedCost cost = cost symbol := by
  classical
  unfold inputCostPointMass FiniteDistribution.expectedCost
  rw [FiniteDistribution.sum_map_mul]
  simp

theorem constrainedInformationValues_nonempty (channel : FiniteChannel X Y)
    (cost : X → ℝ) (budget : ℝ) (hfeasible : ∃ symbol, cost symbol ≤ budget) :
    Set.Nonempty {information | ∃ input : FiniteDistribution X,
      input.IsAdmissibleCost cost budget ∧
        information = channel.mutualInformationBits input} := by
  obtain ⟨symbol, hsymbol⟩ := hfeasible
  refine ⟨_, inputCostPointMass symbol, ?_, rfl⟩
  simpa [FiniteDistribution.IsAdmissibleCost, inputCostPointMass_expectedCost] using hsymbol

theorem constrainedInformationValues_bddAbove (channel : FiniteChannel X Y)
    (cost : X → ℝ) (budget : ℝ) :
    BddAbove {information | ∃ input : FiniteDistribution X,
      input.IsAdmissibleCost cost budget ∧
        information = channel.mutualInformationBits input} := by
  refine ⟨channel.informationCapacityBits, ?_⟩
  rintro value ⟨input, _, rfl⟩
  exact channel.mutualInformationBits_le_informationCapacityBits input

theorem mutualInformationBits_le_constrainedInformationCapacityBits
    (channel : FiniteChannel X Y) (input : FiniteDistribution X)
    {cost : X → ℝ} {budget : ℝ} (hinput : input.IsAdmissibleCost cost budget) :
    channel.mutualInformationBits input ≤
      channel.constrainedInformationCapacityBits cost budget := by
  exact le_csSup (channel.constrainedInformationValues_bddAbove cost budget)
    ⟨input, hinput, rfl⟩

theorem constrainedInformationCapacityBits_nonnegative_of_admissible
    (channel : FiniteChannel X Y) (input : FiniteDistribution X)
    {cost : X → ℝ} {budget : ℝ} (hinput : input.IsAdmissibleCost cost budget) :
    0 ≤ channel.constrainedInformationCapacityBits cost budget := by
  exact (div_nonneg (channel.mutualInformation_nonnegative input)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le).trans
      (channel.mutualInformationBits_le_constrainedInformationCapacityBits input hinput)

theorem constrainedInformationCapacityBits_nonnegative (channel : FiniteChannel X Y)
    (cost : X → ℝ) (budget : ℝ) (hfeasible : ∃ symbol, cost symbol ≤ budget) :
    0 ≤ channel.constrainedInformationCapacityBits cost budget := by
  obtain ⟨symbol, hsymbol⟩ := hfeasible
  apply channel.constrainedInformationCapacityBits_nonnegative_of_admissible
    (inputCostPointMass symbol)
  simpa [FiniteDistribution.IsAdmissibleCost, inputCostPointMass_expectedCost] using hsymbol

theorem exists_input_of_lt_constrainedInformationCapacityBits
    (channel : FiniteChannel X Y) (cost : X → ℝ) (budget : ℝ)
    (hfeasible : ∃ symbol, cost symbol ≤ budget) {rate : ℝ}
    (hrate : rate < channel.constrainedInformationCapacityBits cost budget) :
    ∃ input : FiniteDistribution X,
      input.IsAdmissibleCost cost budget ∧ rate < channel.mutualInformationBits input := by
  obtain ⟨value, ⟨input, hinput, rfl⟩, hvalue⟩ :=
    exists_lt_of_lt_csSup (channel.constrainedInformationValues_nonempty cost budget hfeasible)
      hrate
  exact ⟨input, hinput, hvalue⟩

namespace BlockCode

def inputCostConstant (channel : FiniteChannel X Y) (n : ℕ) (symbol : X) :
    BlockCode channel n where
  messageCount := 1
  messageCount_pos := by decide
  encode _ _ := symbol
  decode _ := 0

theorem inputCostConstant_averageErrorProbability
    (channel : FiniteChannel X Y) (n : ℕ) (symbol : X) :
    (inputCostConstant channel n symbol).averageErrorProbability = 0 := by
  simp [averageErrorProbability, toOneShotCode, OneShotCode.averageErrorProbability,
    OneShotCode.averageSuccessProbability, OneShotCode.successProbability, inputCostConstant]
  rw [sub_eq_zero]
  exact ((channel.block n).row_sum _).symm

theorem inputCostConstant_rate (channel : FiniteChannel X Y) (n : ℕ) (symbol : X) :
    (inputCostConstant channel n symbol).rate = 0 := by
  simp [rate, inputCostConstant]

theorem inputCostConstant_satisfiesInputCost (channel : FiniteChannel X Y)
    {n : ℕ} (hn : 0 < n) (symbol : X) (cost : X → ℝ) (budget : ℝ)
    (hsymbol : cost symbol ≤ budget) :
    (inputCostConstant channel n symbol).SatisfiesInputCost cost budget := by
  have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  intro message
  simpa [codewordCost, inputCostConstant, ← mul_assoc, hnReal] using hsymbol

end BlockCode

theorem constrainedAchievableRate_of_nonpos (channel : FiniteChannel X Y)
    (cost : X → ℝ) (budget : ℝ) (hfeasible : ∃ symbol, cost symbol ≤ budget)
    {rate : ℝ} (hrate : rate ≤ 0) : channel.ConstrainedAchievableRate cost budget rate := by
  obtain ⟨symbol, hsymbol⟩ := hfeasible
  intro ε hε
  refine ⟨1, by omega, ?_⟩
  intro n hn
  exact ⟨BlockCode.inputCostConstant channel n symbol,
    BlockCode.inputCostConstant_satisfiesInputCost channel (by omega) symbol cost budget hsymbol,
    by simpa [BlockCode.inputCostConstant_averageErrorProbability] using hε.le,
    by simpa [BlockCode.inputCostConstant_rate] using hrate⟩

theorem ConstrainedAchievableRate.achievableRate {channel : FiniteChannel X Y}
    {cost : X → ℝ} {budget rate : ℝ}
    (hachievable : channel.ConstrainedAchievableRate cost budget rate) :
    channel.AchievableRate rate := by
  intro ε hε
  obtain ⟨n, hn, hcodes⟩ := hachievable ε hε
  refine ⟨n, hn, ?_⟩
  intro k hk
  obtain ⟨code, _, herror, hrate⟩ := hcodes k hk
  exact ⟨code, herror, hrate⟩

theorem constrainedAchievableRates_bddAbove (channel : FiniteChannel X Y)
    (cost : X → ℝ) (budget : ℝ) :
    BddAbove {rate | channel.ConstrainedAchievableRate cost budget rate} := by
  refine ⟨channel.informationCapacityBits, ?_⟩
  intro rate hrate
  exact channel.hasAchievableRateConverse hrate.achievableRate

theorem constrainedOperationalCapacityBits_nonnegative (channel : FiniteChannel X Y)
    (cost : X → ℝ) (budget : ℝ) (hfeasible : ∃ symbol, cost symbol ≤ budget) :
    0 ≤ channel.constrainedOperationalCapacityBits cost budget := by
  exact le_csSup (channel.constrainedAchievableRates_bddAbove cost budget)
    (channel.constrainedAchievableRate_of_nonpos cost budget hfeasible le_rfl)

theorem block_mutualInformation_le_sum_coordinateMutualInformation
    (channel : FiniteChannel X Y) (n : ℕ)
    (input : FiniteDistribution (Fin n → X)) :
    (channel.block n).mutualInformation input ≤
      ∑ coordinate : Fin n,
        channel.mutualInformation (input.coordinateMarginal coordinate) := by
  exact channel.block_mutualInformation_le_sum_coordinate n input

namespace BlockCode

noncomputable def inputCoordinateMixture [DecidableEq X] {channel : FiniteChannel X Y} {n : ℕ}
    (code : BlockCode channel n) (hn : 0 < n) : FiniteDistribution X := by
  letI : NeZero n := ⟨hn.ne'⟩
  letI : Nonempty (Fin code.messageCount) := Fin.pos_iff_nonempty.mp code.messageCount_pos
  exact ((FiniteDistribution.uniform (Fin code.messageCount)).map code.encode).averageCoordinateMarginal

theorem inputCoordinateMixture_expectedCost [DecidableEq X] {channel : FiniteChannel X Y} {n : ℕ}
    (code : BlockCode channel n) (hn : 0 < n) (cost : X → ℝ) :
    (code.inputCoordinateMixture hn).expectedCost cost =
      (code.messageCount : ℝ)⁻¹ * ∑ message, code.codewordCost cost message := by
  classical
  simp only [inputCoordinateMixture, FiniteDistribution.averageCoordinateMarginal,
    FiniteDistribution.expectedCost,
    FiniteDistribution.sum_mixture_mul, FiniteDistribution.coordinateMarginal,
    FiniteDistribution.sum_map_mul, FiniteDistribution.uniform_apply, Fintype.card_fin,
    codewordCost, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro message
  apply Fintype.sum_congr
  intro coordinate
  ring

theorem inputCoordinateMixture_isAdmissibleCost [DecidableEq X]
    {channel : FiniteChannel X Y} {n : ℕ}
    (code : BlockCode channel n) (hn : 0 < n) {cost : X → ℝ} {budget : ℝ}
    (hcost : code.SatisfiesInputCost cost budget) :
    (code.inputCoordinateMixture hn).IsAdmissibleCost cost budget := by
  have hcount : (code.messageCount : ℝ) ≠ 0 := by
    exact_mod_cast code.messageCount_pos.ne'
  unfold FiniteDistribution.IsAdmissibleCost
  rw [code.inputCoordinateMixture_expectedCost]
  calc
    (code.messageCount : ℝ)⁻¹ * ∑ message, code.codewordCost cost message ≤
        (code.messageCount : ℝ)⁻¹ * ∑ _message : Fin code.messageCount, budget := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun message _ ↦ hcost message)
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = budget := by simp [hcount]

end BlockCode

theorem blockCode_mutualInformation_le_constrainedInformationCapacityBits [DecidableEq X]
    (channel : FiniteChannel X Y) {n : ℕ} (code : BlockCode channel n)
    (hn : 0 < n) {cost : X → ℝ} {budget : ℝ}
    (hcost : code.SatisfiesInputCost cost budget) :
    letI : Nonempty (Fin code.messageCount) := Fin.pos_iff_nonempty.mp code.messageCount_pos
    (channel.block n).mutualInformation
      ((FiniteDistribution.uniform (Fin code.messageCount)).map code.encode) ≤
      (n : ℝ) * channel.constrainedInformationCapacityBits cost budget * Real.log 2 := by
  letI : NeZero n := ⟨hn.ne'⟩
  letI : Nonempty (Fin code.messageCount) := Fin.pos_iff_nonempty.mp code.messageCount_pos
  let input := (FiniteDistribution.uniform (Fin code.messageCount)).map code.encode
  have hblock := channel.block_mutualInformation_le_mul_averageCoordinateMarginal input
  change (channel.block n).mutualInformation input ≤
    (n : ℝ) * channel.mutualInformation (code.inputCoordinateMixture hn) at hblock
  have hsingle := channel.mutualInformationBits_le_constrainedInformationCapacityBits
    (code.inputCoordinateMixture hn) (code.inputCoordinateMixture_isAdmissibleCost hn hcost)
  have hsingleNats : channel.mutualInformation (code.inputCoordinateMixture hn) ≤
      channel.constrainedInformationCapacityBits cost budget * Real.log 2 :=
    (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp hsingle
  exact hblock.trans (by simpa [mul_assoc] using
    mul_le_mul_of_nonneg_left hsingleNats (Nat.cast_nonneg n : (0 : ℝ) ≤ n))

theorem blockCode_log_messageCount_le_constrainedInformationCapacityBits
    (channel : FiniteChannel X Y) {n : ℕ} (code : BlockCode channel n)
    (hn : 0 < n) {cost : X → ℝ} {budget : ℝ}
    (hcost : code.SatisfiesInputCost cost budget) :
    Real.log code.messageCount ≤
      (n : ℝ) * channel.constrainedInformationCapacityBits cost budget * Real.log 2 + Real.log 2 +
        code.averageErrorProbability * Real.log code.messageCount := by
  classical
  letI : Nonempty (Fin code.messageCount) := Fin.pos_iff_nonempty.mp code.messageCount_pos
  have hfano := ((channel.block n).encoded code.encode).fano_uniform code.decode
  simp only [Fintype.card_fin] at hfano
  change Real.log code.messageCount ≤
    ((channel.block n).encoded code.encode).mutualInformation
      (FiniteDistribution.uniform (Fin code.messageCount)) + Real.log 2 +
        code.averageErrorProbability * Real.log code.messageCount at hfano
  rw [encoded_mutualInformation] at hfano
  have hmutual := channel.blockCode_mutualInformation_le_constrainedInformationCapacityBits
    code hn hcost
  linarith

theorem blockCode_constrained_rate_bound (channel : FiniteChannel X Y)
    {n : ℕ} (code : BlockCode channel n) (hn : 0 < n)
    {cost : X → ℝ} {budget : ℝ} (hcost : code.SatisfiesInputCost cost budget) :
    (1 - code.averageErrorProbability) * code.rate ≤
      channel.constrainedInformationCapacityBits cost budget + (n : ℝ)⁻¹ := by
  exact fano_rate_bound hn
    (channel.blockCode_log_messageCount_le_constrainedInformationCapacityBits code hn hcost)

theorem ConstrainedAchievableRate.le_constrainedInformationCapacityBits
    (channel : FiniteChannel X Y) {cost : X → ℝ} {budget rate : ℝ}
    (hfeasible : ∃ symbol, cost symbol ≤ budget)
    (hachievable : channel.ConstrainedAchievableRate cost budget rate) :
    rate ≤ channel.constrainedInformationCapacityBits cost budget := by
  apply rate_le_of_fano_bounds
    (channel.constrainedInformationCapacityBits_nonnegative cost budget hfeasible)
  intro hrate ε hε hεlt
  obtain ⟨firstBlocklength, hfirstPositive, hcodes⟩ := hachievable ε hε
  filter_upwards [Filter.eventually_ge_atTop firstBlocklength] with n hn
  obtain ⟨code, hcost, herror, hcodeRate⟩ := hcodes n hn
  exact fano_rate_bound_of_error_le hrate hεlt herror hcodeRate
    (channel.blockCode_constrained_rate_bound code (lt_of_lt_of_le hfirstPositive hn) hcost)

theorem constrainedOperationalCapacityBits_le_constrainedInformationCapacityBits
    (channel : FiniteChannel X Y) (cost : X → ℝ) (budget : ℝ)
    (hfeasible : ∃ symbol, cost symbol ≤ budget) :
    channel.constrainedOperationalCapacityBits cost budget ≤
      channel.constrainedInformationCapacityBits cost budget := by
  apply csSup_le
  · exact ⟨0, channel.constrainedAchievableRate_of_nonpos cost budget hfeasible le_rfl⟩
  · intro rate hrate
    exact ConstrainedAchievableRate.le_constrainedInformationCapacityBits channel hfeasible hrate

end CapacityAtlas.FiniteChannel
