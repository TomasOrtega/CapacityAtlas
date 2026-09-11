/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.

Adapted from TomasOrtega/CapacityAtlasInputCost, commit 5e6a432bc276aa4e08b7f27658daf40e029cda48,
CapacityAtlasCost/Capacity.lean. Imports and certificate types use the monorepo modules.
-/

import CapacityAtlasForMathlib.InformationTheory.InputCost.ConstrainedCoding
import CapacityAtlasForMathlib.InformationTheory.InputCost.InputApproximation
import CapacityAtlasForMathlib.InformationTheory.InputCost.Attainment

namespace CapacityAtlasCost

open CapacityAtlas

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem achievableRate_of_admissible_input (channel : FiniteChannel X Y)
    (input : FiniteDistribution X) (cost : X → ℝ) (budget : ℝ)
    (hfeasible : ∃ symbol, cost symbol ≤ budget)
    (hinput : input.IsAdmissibleCost cost budget) {rate : ℝ}
    (hrate : rate < channel.mutualInformationBits input) :
    channel.ConstrainedAchievableRate cost budget rate := by
  by_cases hcheap : ∃ point, cost point < budget
  · obtain ⟨improved, hcost, hrate⟩ :=
      channel.exists_strictCost_input_of_lt_mutualInformationBits input cost budget
        hinput hcheap hrate
    exact channel.constrainedAchievableRate_of_lt_mutualInformationBits_of_badCostMass_tendsto_zero
      improved cost budget hfeasible (badCostMass_tendsto_zero improved cost budget hcost) hrate
  · have hlower : ∀ x, budget ≤ cost x := fun x ↦
      le_of_not_gt (fun h ↦ hcheap ⟨x, h⟩)
    have htail : Filter.Tendsto (badCostMass input cost budget) Filter.atTop (nhds 0) := by
      have heq : badCostMass input cost budget = fun _ ↦ 0 :=
        funext (badCostMass_eq_zero input cost budget hlower hinput)
      rw [heq]
      exact tendsto_const_nhds
    exact channel.constrainedAchievableRate_of_lt_mutualInformationBits_of_badCostMass_tendsto_zero
      input cost budget hfeasible htail hrate

theorem achievableRate_of_lt_constrainedInformationCapacityBits
    (channel : FiniteChannel X Y) (cost : X → ℝ) (budget : ℝ)
    (hfeasible : ∃ symbol, cost symbol ≤ budget) {rate : ℝ}
    (hrate : rate < channel.constrainedInformationCapacityBits cost budget) :
    channel.ConstrainedAchievableRate cost budget rate := by
  obtain ⟨input, hinput, hrateInput⟩ :=
    channel.exists_input_of_lt_constrainedInformationCapacityBits cost budget hfeasible hrate
  exact achievableRate_of_admissible_input channel input cost budget hfeasible hinput hrateInput

/-- Certificate for the unchanged Atlas exact-capacity claim, version 1. -/
theorem finiteDMCInputCostCapacity (channel : FiniteChannel X Y)
    (cost : X → ℝ) (budget : ℝ) :
    (∀ symbol, 0 ≤ cost symbol) →
      (∃ symbol, cost symbol ≤ budget) →
        channel.constrainedOperationalCapacityBits cost budget =
          channel.constrainedInformationCapacityBits cost budget := by
  intro _ hfeasible
  apply le_antisymm
  · exact channel.constrainedOperationalCapacityBits_le_constrainedInformationCapacityBits
      cost budget hfeasible
  · apply le_of_forall_lt_imp_le_of_dense
    intro rate hrate
    exact le_csSup (channel.constrainedAchievableRates_bddAbove cost budget)
      (achievableRate_of_lt_constrainedInformationCapacityBits channel cost budget hfeasible hrate)

/-- The information supremum is a maximum and equals operational capacity. -/
theorem exists_capacityAchieving_input (channel : FiniteChannel X Y)
    (cost : X → ℝ) (budget : ℝ) (hcost : ∀ symbol, 0 ≤ cost symbol)
    (hfeasible : ∃ symbol, cost symbol ≤ budget) :
    ∃ input : FiniteDistribution X, input.IsAdmissibleCost cost budget ∧
      channel.mutualInformationBits input = channel.constrainedOperationalCapacityBits cost budget := by
  rw [finiteDMCInputCostCapacity channel cost budget hcost hfeasible]
  exact channel.exists_admissible_input_attaining_constrainedInformationCapacityBits
    cost budget hfeasible

end CapacityAtlasCost
