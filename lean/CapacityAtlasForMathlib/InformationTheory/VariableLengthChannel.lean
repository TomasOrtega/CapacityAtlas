/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteChannelCapacity

open scoped BigOperators

namespace CapacityAtlas

/-- A finite-support variable-length one-step channel. -/
structure VariableLengthChannelStep (X Y : Type*) [Fintype X] [Fintype Y]
    [DecidableEq Y] where
  support : X → Finset (List Y)
  transition : X → List Y → ℝ
  nonnegative : ∀ input output, 0 ≤ transition input output
  row_sum : ∀ input, ∑ output ∈ support input, transition input output = 1
  zero_outside : ∀ input output, output ∉ support input → transition input output = 0

end CapacityAtlas
