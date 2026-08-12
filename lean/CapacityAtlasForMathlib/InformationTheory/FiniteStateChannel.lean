/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteChannelCapacity

open scoped BigOperators

namespace CapacityAtlas

/-- A finite-state one-step channel, including its next-state transition. -/
@[capacity_shared_api]
structure FiniteStateChannel (X State Y : Type*)
    [Fintype X] [Fintype State] [Fintype Y] where
  transition : X → State → Y → State → ℝ
  nonnegative : ∀ input state output nextState,
    0 ≤ transition input state output nextState
  row_sum : ∀ input state, ∑ output, ∑ nextState,
    transition input state output nextState = 1

end CapacityAtlas
