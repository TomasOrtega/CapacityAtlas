/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.WiretapOperational

namespace CapacityAtlas.Claims

/-- The general auxiliary-variable strong-secrecy capacity formula. -/
@[capacity_problem "general-finite-wiretap-channel", capacity_claim "operational-capacity" 1,
  capacity_statement, capacity_solved]
theorem generalWiretap {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Nonempty X] [Nonempty Y] [Nonempty Z] (W : FiniteWiretapChannel X Y Z) :
    WiretapOperational.capacity W = finiteWiretapAuxiliaryCapacity W := by
  sorry

end CapacityAtlas.Claims
