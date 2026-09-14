/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.MACFeedbackModel

namespace CapacityAtlas.Claims

/-- Cover--Leung achievability and dependence balance for a common-output finite feedback MAC. -/
@[capacity_problem "multiple-access-channel-with-feedback", capacity_claim "cover-leung-dependence-balance" 1,
  capacity_statement, capacity_solved]
theorem macFeedbackBounds {X₁ X₂ Y : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y]
    [Nonempty X₁] [Nonempty X₂] [Nonempty Y] (W : FiniteChannel (X₁ × X₂) Y) :
    MACFeedback.coverLeung W ⊆ MACFeedback.capacityRegion W ∧
      MACFeedback.capacityRegion W ⊆ MACFeedback.dependenceBalance W := by
  sorry

/-- Independently tracked cover leung achievability. -/
@[capacity_problem "multiple-access-channel-with-feedback", capacity_claim "cover-leung-achievability" 1,
  capacity_statement, capacity_solved]
theorem macFeedbackCoverLeung {X₁ X₂ Y : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y]
    [Nonempty X₁] [Nonempty X₂] [Nonempty Y] (W : FiniteChannel (X₁ × X₂) Y) :
    MACFeedback.coverLeung W ⊆ MACFeedback.capacityRegion W := by
  sorry

/-- Independently tracked dependence balance converse. -/
@[capacity_problem "multiple-access-channel-with-feedback", capacity_claim "dependence-balance-converse" 1,
  capacity_statement, capacity_solved]
theorem macFeedbackDependenceBalance {X₁ X₂ Y : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y]
    [Nonempty X₁] [Nonempty X₂] [Nonempty Y] (W : FiniteChannel (X₁ × X₂) Y) :
    MACFeedback.capacityRegion W ⊆ MACFeedback.dependenceBalance W := by
  sorry

end CapacityAtlas.Claims
