/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0

Adapted from TomasOrtega/CapacityAtlasInputCost, commit 5e6a432bc276aa4e08b7f27658daf40e029cda48,
CapacityAtlasCost/ConstrainedCoding.lean. Reuses shared random-coding estimates.
-/

import CapacityAtlasForMathlib.InformationTheory.InputCost.CostTail
import CapacityAtlasForMathlib.InformationTheory.InputCost.Converse
import CapacityAtlasForMathlib.InformationTheory.RandomCoding

open scoped BigOperators

namespace CapacityAtlas.FiniteChannel

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem exists_constrainedBlockCode_averageErrorProbability_le
    (channel : FiniteChannel X Y) (input : FiniteDistribution X)
    (cost : X → ℝ) (budget : ℝ) (hfeasible : ∃ symbol, cost symbol ≤ budget)
    (δ : ℝ) {blocklength messages : ℕ}
    (hblocklength : 0 < blocklength) (hmessageCount : 0 < messages) (hδ : 0 < δ) :
    ∃ code : BlockCode channel blocklength,
      code.messageCount = messages ∧ code.SatisfiesInputCost cost budget ∧
        code.averageErrorProbability ≤
          ((blocklength : ℝ) * channel.informationVariance input) /
              (((blocklength : ℝ) * δ) ^ 2) +
            (messages : ℝ) * Real.exp
              (-((blocklength : ℝ) * channel.mutualInformation input -
                (blocklength : ℝ) * δ)) +
              CapacityAtlasCost.badCostMass input cost budget blocklength := by
  classical
  obtain ⟨symbol, hsymbol⟩ := hfeasible
  letI : Nonempty (Fin messages) := Fin.pos_iff_nonempty.mp hmessageCount
  let threshold :=
    (blocklength : ℝ) * channel.mutualInformation input - (blocklength : ℝ) * δ
  let allowed : (Fin blocklength → X) → Prop := fun word ↦
    (∑ i, cost (word i)) ≤ (blocklength : ℝ) * budget
  have hfallback : allowed (fun _ ↦ symbol) := by
    simpa [allowed] using mul_le_mul_of_nonneg_left hsymbol
      (Nat.cast_nonneg blocklength : (0 : ℝ) ≤ blocklength)
  obtain ⟨oneShot, hallowed, honeShot⟩ :=
    (channel.block blocklength).exists_oneShotCode_averageErrorProbability_le_of_allowed
      (input.iid blocklength) threshold allowed (fun _ ↦ symbol) hfallback (M := Fin messages)
  let code : BlockCode channel blocklength :=
    { messageCount := messages
      messageCount_pos := hmessageCount
      encode := oneShot.encode
      decode := oneShot.decode }
  have hnReal : 0 < (blocklength : ℝ) := by exact_mod_cast hblocklength
  have htail :
      (channel.block blocklength).informationDensityLowerTailMass
          (input.iid blocklength) threshold ≤
        ((blocklength : ℝ) * channel.informationVariance input) /
          (((blocklength : ℝ) * δ) ^ 2) := by
    rw [channel.block_informationDensityLowerTailMass_eq input blocklength threshold]
    exact channel.blockInformationDensity_lowerTail_le input hblocklength hδ
  have hbad : (∑ word, input.iid blocklength word * (if allowed word then 0 else 1)) =
      CapacityAtlasCost.badCostMass input cost budget blocklength := by
    unfold CapacityAtlasCost.badCostMass
    apply Fintype.sum_congr
    intro word
    by_cases hword : allowed word
    · simp [hword, allowed, not_lt.mpr hword]
    · have hgt : (blocklength : ℝ) * budget < ∑ i, cost (word i) := lt_of_not_ge hword
      simp [hword, hgt]
  refine ⟨code, rfl, ?_, ?_⟩
  · intro message
    change (blocklength : ℝ)⁻¹ * (∑ i, cost (oneShot.encode message i)) ≤ budget
    rw [← div_eq_inv_mul]
    exact (div_le_iff₀ hnReal).2 (by simpa [allowed, mul_comm] using hallowed message)
  · rw [hbad] at honeShot
    have hselected := honeShot.trans
      (add_le_add_left (add_le_add_left htail _) _)
    simpa [code, BlockCode.averageErrorProbability, BlockCode.toOneShotCode, threshold]
      using hselected

theorem constrainedAchievableRate_of_lt_mutualInformationBits_of_badCostMass_tendsto_zero
    (channel : FiniteChannel X Y) (input : FiniteDistribution X)
    (cost : X → ℝ) (budget : ℝ) (hfeasible : ∃ symbol, cost symbol ≤ budget)
    (htailTendsto : Filter.Tendsto (CapacityAtlasCost.badCostMass input cost budget)
      Filter.atTop (nhds 0))
    {rate : ℝ} (hrate : rate < channel.mutualInformationBits input) :
    channel.ConstrainedAchievableRate cost budget rate := by
  by_cases hrateNonpos : rate ≤ 0
  · exact channel.constrainedAchievableRate_of_nonpos cost budget hfeasible hrateNonpos
  have hratePos : 0 < rate := lt_of_not_ge hrateNonpos
  let information := channel.mutualInformation input
  let logTwo := Real.log 2
  let gap := information - rate * logTwo
  let δ := gap / 2
  have hlogTwo : 0 < logTwo := Real.log_pos (by norm_num)
  have hrateNats : rate * logTwo < information := by
    apply (lt_div_iff₀ hlogTwo).mp
    simpa [FiniteChannel.mutualInformationBits, information, logTwo] using hrate
  have hgap : 0 < gap := by
    dsimp [gap]
    linarith
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  intro ε hε
  let variance := channel.informationVariance input
  have hbound : Filter.Tendsto
      (fun blocklength : ℕ ↦
        ((blocklength : ℝ) * variance) / (((blocklength : ℝ) * δ) ^ 2) +
          2 * Real.exp (-((blocklength : ℝ) * δ)) +
            CapacityAtlasCost.badCostMass input cost budget blocklength)
      Filter.atTop (nhds 0) := by
    simpa using (randomCodingAsymptoticBound_tendsto_zero variance δ hδ).add htailTendsto
  have heventually :
      ∀ᶠ blocklength : ℕ in Filter.atTop,
        ((blocklength : ℝ) * variance) / (((blocklength : ℝ) * δ) ^ 2) +
            2 * Real.exp (-((blocklength : ℝ) * δ)) +
              CapacityAtlasCost.badCostMass input cost budget blocklength < ε :=
    (tendsto_order.1 hbound).2 ε hε
  obtain ⟨firstBound, hfirstBound⟩ := Filter.eventually_atTop.1 heventually
  refine ⟨max 1 firstBound, by omega, ?_⟩
  intro blocklength hblocklength
  have hblocklengthPos : 0 < blocklength := lt_of_lt_of_le (by omega) hblocklength
  let messageCount := messageCountAtRate rate blocklength
  have hmessageCount : 0 < messageCount := messageCountAtRate_pos rate blocklength
  obtain ⟨code, hcodeCount, hcodeCost, hcodeError⟩ :=
    channel.exists_constrainedBlockCode_averageErrorProbability_le
      input cost budget hfeasible δ hblocklengthPos hmessageCount hδ
  refine ⟨code, hcodeCost, ?_, ?_⟩
  · have hexponential :
        (messageCount : ℝ) * Real.exp
            (-((blocklength : ℝ) * channel.mutualInformation input -
              (blocklength : ℝ) * δ)) ≤
          2 * Real.exp (-((blocklength : ℝ) * δ)) :=
      messageCountAtRate_mul_exp_neg_le rate δ hratePos.le blocklength (by
        dsimp [δ, gap, information, logTwo]
        linarith)
    have herrorBound :
        ((blocklength : ℝ) * variance) / (((blocklength : ℝ) * δ) ^ 2) +
            (messageCount : ℝ) * Real.exp
              (-((blocklength : ℝ) * channel.mutualInformation input -
                (blocklength : ℝ) * δ)) ≤
          ((blocklength : ℝ) * variance) / (((blocklength : ℝ) * δ) ^ 2) +
            2 * Real.exp (-((blocklength : ℝ) * δ)) :=
      add_le_add_right hexponential _
    exact hcodeError.trans
      ((add_le_add_left herrorBound (CapacityAtlasCost.badCostMass input cost budget blocklength)).trans
        (hfirstBound blocklength (le_trans (Nat.le_max_right _ _) hblocklength)).le)
  · rw [BlockCode.rate, hcodeCount]
    exact targetRate_le_rateOfMessageCountAtRate rate hblocklengthPos

end CapacityAtlas.FiniteChannel
