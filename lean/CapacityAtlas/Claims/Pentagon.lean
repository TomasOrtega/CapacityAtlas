/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.FiniteZeroError

namespace CapacityAtlas.Claims

/-- Both the graph growth constant and operational zero-error capacity of the pentagon typewriter. -/
@[capacity_problem "pentagon-zero-error-channel", capacity_claim "operational-capacity" 1,
  capacity_statement, capacity_solved]
theorem pentagon :
    FiniteZeroError.cycleGrowth 5 = Real.sqrt 5 ∧
      FiniteZeroError.capacity (FiniteZeroError.typewriter 5) = (1 / 2 : ℝ) * Real.logb 2 5 := by
  sorry

/-- Independently tracked graph capacity. -/
@[capacity_problem "pentagon-zero-error-channel", capacity_claim "graph-capacity" 1,
  capacity_statement, capacity_solved]
theorem pentagonGraph :
    FiniteZeroError.cycleGrowth 5 = Real.sqrt 5 := by
  sorry

/-- Independently tracked typewriter capacity. -/
@[capacity_problem "pentagon-zero-error-channel", capacity_claim "typewriter-capacity" 1,
  capacity_statement, capacity_solved]
theorem pentagonTypewriter :
    FiniteZeroError.capacity (FiniteZeroError.typewriter 5) = (1 / 2 : ℝ) * Real.logb 2 5 := by
  sorry

end CapacityAtlas.Claims
