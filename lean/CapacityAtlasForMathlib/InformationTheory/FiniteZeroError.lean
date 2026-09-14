/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.OperationalRegion
import CapacityAtlasForMathlib.InformationTheory.CodingConverse
import CapacityAtlasForMathlib.InformationTheory.GraphZeroError
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

namespace CapacityAtlas.FiniteZeroError

/-- Exactly zero error at every blocklength in the sequence. -/
noncomputable def capacity {X Y : Type*} [Fintype X] [Fintype Y]
    (W : FiniteChannel X Y) : ℝ :=
  Operational.capacity (FiniteChannel.BlockCode W)
    (fun _ c ↦ c.averageErrorProbability = 0) (fun _ _ ↦ 0)
    (fun _ c ↦ c.rate)

/-- The physical typewriter law: x or x+1, each with probability one half. -/
noncomputable def typewriter (k : ℕ) [NeZero k] : FiniteChannel (Fin k) (Fin k) := by
  classical
  exact FiniteChannel.ofRows fun x ↦
    (FiniteDistribution.uniform Bool).map (fun b ↦ if b then x + 1 else x)

noncomputable def cycleGrowth (k : ℕ) : ℝ := by
  classical
  exact graphShannonCapacity (SimpleGraph.cycleGraph k).Adj

end CapacityAtlas.FiniteZeroError
