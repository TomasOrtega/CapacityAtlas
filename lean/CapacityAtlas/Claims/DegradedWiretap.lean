/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.WiretapOperational

namespace CapacityAtlas.Claims

/-- The degraded finite wiretap formula with unnormalized leakage tending to zero. -/
@[capacity_problem "degraded-wiretap-channel", capacity_claim "operational-capacity" 1,
  capacity_statement, capacity_solved]
theorem degradedWiretap {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Nonempty X] [Nonempty Y] [Nonempty Z] (W : FiniteWiretapChannel X Y Z) (hW : WiretapOperational.IsDegraded W) :
    WiretapOperational.capacity W = WiretapOperational.degradedInformationCapacity W := by
  sorry

end CapacityAtlas.Claims
