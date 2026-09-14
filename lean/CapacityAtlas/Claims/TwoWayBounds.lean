/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.Network.InteractiveTwoWay

namespace CapacityAtlas.Claims

/-- Shannon's fixed nonadaptive inner region and adaptive outer region. -/
@[capacity_problem "discrete-memoryless-two-way-channel", capacity_claim "shannon-inner-outer" 1,
  capacity_statement, capacity_solved]
theorem twoWayBounds {A B Y Z : Type*} [Fintype A] [Fintype B] [Fintype Y] [Fintype Z]
    [Nonempty A] [Nonempty B] [Nonempty Y] [Nonempty Z]
    (W : FiniteChannel (A × B) (Y × Z)) :
    TwoWay.shannonInner W ⊆ TwoWay.capacityRegion W ∧
      TwoWay.capacityRegion W ⊆ TwoWay.shannonOuter W := by
  sorry

/-- Independently tracked shannon achievability. -/
@[capacity_problem "discrete-memoryless-two-way-channel", capacity_claim "shannon-achievability" 1,
  capacity_statement, capacity_solved]
theorem twoWayShannonInner {A B Y Z : Type*} [Fintype A] [Fintype B] [Fintype Y] [Fintype Z]
    [Nonempty A] [Nonempty B] [Nonempty Y] [Nonempty Z]
    (W : FiniteChannel (A × B) (Y × Z)) :
    TwoWay.shannonInner W ⊆ TwoWay.capacityRegion W := by
  sorry

/-- Independently tracked shannon converse. -/
@[capacity_problem "discrete-memoryless-two-way-channel", capacity_claim "shannon-converse" 1,
  capacity_statement, capacity_solved]
theorem twoWayShannonOuter {A B Y Z : Type*} [Fintype A] [Fintype B] [Fintype Y] [Fintype Z]
    [Nonempty A] [Nonempty B] [Nonempty Y] [Nonempty Z]
    (W : FiniteChannel (A × B) (Y × Z)) :
    TwoWay.capacityRegion W ⊆ TwoWay.shannonOuter W := by
  sorry

end CapacityAtlas.Claims
