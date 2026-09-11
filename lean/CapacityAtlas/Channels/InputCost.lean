/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.InputCost.Capacity

namespace CapacityAtlas.FiniteChannel

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The finite-DMC coding theorem with a feasible nonnegative input-cost constraint. -/
@[capacity_problem "finite-dmc-input-cost", capacity_statement, capacity_solved,
  capacity_claim "exact-capacity" 1, capacity_formal_proof]
theorem finiteDMCInputCostCapacityStatement (channel : FiniteChannel X Y)
    (cost : X → ℝ) (budget : ℝ) :
  (∀ symbol, 0 ≤ cost symbol) →
    (∃ symbol, cost symbol ≤ budget) →
      channel.constrainedOperationalCapacityBits cost budget =
        channel.constrainedInformationCapacityBits cost budget :=
  CapacityAtlasCost.finiteDMCInputCostCapacity channel cost budget

end CapacityAtlas.FiniteChannel
