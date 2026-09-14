/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.ArbitrarilyVarying

namespace CapacityAtlas.Claims

/-- The unconstrained deterministic average-error AVC dichotomy. The jammer does not see the message. -/
@[capacity_problem "arbitrarily-varying-discrete-memoryless-channel", capacity_claim "operational-capacity" 1,
  capacity_statement, capacity_solved]
theorem arbitrarilyVarying {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]
    [Nonempty S] [Nonempty X] [Nonempty Y] (W : S → FiniteChannel X Y) :
    (ArbitrarilyVarying.Symmetrizable W → ArbitrarilyVarying.capacity W = 0) ∧
      (¬ArbitrarilyVarying.Symmetrizable W →
        ArbitrarilyVarying.capacity W = ArbitrarilyVarying.randomCodeValue W) := by
  sorry

end CapacityAtlas.Claims
