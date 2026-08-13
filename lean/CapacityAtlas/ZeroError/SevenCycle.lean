/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GraphZeroError
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace CapacityAtlas.ZeroError

open CapacityAtlas

def sevenCycleAdjacent (left right : Fin 7) : Prop :=
  left.val = (right.val + 1) % 7 ∨ right.val = (left.val + 1) % 7

instance : DecidableRel sevenCycleAdjacent := fun left right ↦ by
  unfold sevenCycleAdjacent
  infer_instance

@[capacity_problem "seven-cycle-zero-error-channel", capacity_definition]
noncomputable def sevenCycleShannonCapacity : ℝ :=
  graphShannonCapacity sevenCycleAdjacent

/-- The sourced finite-power lower certificate and Lovasz-theta upper bound. -/
@[capacity_problem "seven-cycle-zero-error-channel", capacity_statement, capacity_solved,
  capacity_claim "capacity-bounds" 1]
theorem sevenCycleKnownBounds :
  Real.rpow 367 ((5 : ℝ)⁻¹) ≤ sevenCycleShannonCapacity ∧
    sevenCycleShannonCapacity ≤
      7 * Real.cos (Real.pi / 7) / (1 + Real.cos (Real.pi / 7)) := by
  sorry

end CapacityAtlas.ZeroError
