/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.FiniteStateOperational

namespace CapacityAtlas.Claims

/-- Stationary primitive Markov additive noise subtracts its entropy rate from log alphabet size. -/
@[capacity_problem "finite-group-markov-noise-channel", capacity_claim "operational-capacity" 2,
  capacity_statement, capacity_solved]
theorem markovNoise {G : Type*} [Fintype G] [AddCommGroup G]
    (K : FiniteChannel G G) (p : FiniteDistribution G)
    (hp : K.outputDistribution p = p) (hK : FiniteStateOperational.IsPrimitive K) :
    FiniteStateOperational.capacity (FiniteStateOperational.additiveMarkov K) p (fun _ _ ↦ True) =
      Real.logb 2 (Fintype.card G) - FiniteStateOperational.markovEntropyRate p K := by
  sorry

end CapacityAtlas.Claims
