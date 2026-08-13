/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.OperationalCapacity

open scoped BigOperators

namespace CapacityAtlas.FiniteChannel

variable {X Y : Type*} [Fintype X] [Fintype Y]

namespace BlockCode

/-- Average input cost of one codeword. -/
@[capacity_problem "finite-dmc-input-cost", capacity_definition]
noncomputable def codewordCost {channel : FiniteChannel X Y} {blocklength : ℕ}
    (cost : X → ℝ) (code : BlockCode channel blocklength)
    (message : Fin code.messageCount) : ℝ :=
  (blocklength : ℝ)⁻¹ * ∑ coordinate, cost (code.encode message coordinate)

/-- The maximum-codeword input-cost constraint. -/
@[capacity_problem "finite-dmc-input-cost", capacity_definition]
def SatisfiesInputCost {channel : FiniteChannel X Y} {blocklength : ℕ}
    (cost : X → ℝ) (budget : ℝ) (code : BlockCode channel blocklength) : Prop :=
  ∀ message, code.codewordCost cost message ≤ budget

end BlockCode

/-- Vanishing-average-error achievability subject to a maximum-codeword cost budget. -/
@[capacity_problem "finite-dmc-input-cost", capacity_definition]
def ConstrainedAchievableRate (channel : FiniteChannel X Y)
    (cost : X → ℝ) (budget rate : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ firstBlocklength : ℕ, 0 < firstBlocklength ∧
    ∀ blocklength, firstBlocklength ≤ blocklength →
      ∃ code : BlockCode channel blocklength,
        code.SatisfiesInputCost cost budget ∧
          code.averageErrorProbability ≤ ε ∧ rate ≤ code.rate

/-- Operational average-error capacity under a maximum-codeword input-cost constraint. -/
@[capacity_problem "finite-dmc-input-cost", capacity_definition]
noncomputable def constrainedOperationalCapacityBits (channel : FiniteChannel X Y)
    (cost : X → ℝ) (budget : ℝ) : ℝ :=
  sSup {rate | channel.ConstrainedAchievableRate cost budget rate}

/-- Expected one-letter input cost. -/
@[capacity_problem "finite-dmc-input-cost", capacity_definition]
noncomputable def _root_.CapacityAtlas.FiniteDistribution.expectedCost
    (input : FiniteDistribution X) (cost : X → ℝ) : ℝ :=
  ∑ symbol, input symbol * cost symbol

/-- Input distributions satisfying the expected-cost budget. -/
@[capacity_problem "finite-dmc-input-cost", capacity_definition]
def _root_.CapacityAtlas.FiniteDistribution.IsAdmissibleCost
    (input : FiniteDistribution X) (cost : X → ℝ) (budget : ℝ) : Prop :=
  input.expectedCost cost ≤ budget

/-- The constrained mutual-information supremum in bits per channel use. -/
@[capacity_problem "finite-dmc-input-cost", capacity_definition]
noncomputable def constrainedInformationCapacityBits (channel : FiniteChannel X Y)
    (cost : X → ℝ) (budget : ℝ) : ℝ :=
  sSup {information | ∃ input : FiniteDistribution X,
    input.IsAdmissibleCost cost budget ∧
      information = channel.mutualInformationBits input}

/-- The finite-DMC coding theorem with a feasible nonnegative input-cost constraint. -/
@[capacity_problem "finite-dmc-input-cost", capacity_statement, capacity_solved]
theorem finiteDMCInputCostCapacityStatement (channel : FiniteChannel X Y)
    (cost : X → ℝ) (budget : ℝ) :
  (∀ symbol, 0 ≤ cost symbol) →
    (∃ symbol, cost symbol ≤ budget) →
      channel.constrainedOperationalCapacityBits cost budget =
        channel.constrainedInformationCapacityBits cost budget := by
  sorry

end CapacityAtlas.FiniteChannel
