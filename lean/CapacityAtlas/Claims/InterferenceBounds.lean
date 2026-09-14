/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.Network.InterferenceOperational

namespace CapacityAtlas.Claims

/-- A fixed Han--Kobayashi inner region and cooperative cut-set outer region. -/
@[capacity_problem "general-two-user-interference-channel", capacity_claim "han-kobayashi-cut-set" 1,
  capacity_statement, capacity_solved]
theorem interferenceBounds {X₁ X₂ Y₁ Y₂ : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
    [Nonempty X₁] [Nonempty X₂] [Nonempty Y₁] [Nonempty Y₂]
    (W : FiniteInterferenceChannel X₁ X₂ Y₁ Y₂) :
    Interference.hanKobayashi W ⊆ Interference.capacityRegion W ∧
      Interference.capacityRegion W ⊆ Interference.cutSet W := by
  sorry

/-- Independently tracked han kobayashi achievability. -/
@[capacity_problem "general-two-user-interference-channel", capacity_claim "han-kobayashi-achievability" 1,
  capacity_statement, capacity_solved]
theorem interferenceHanKobayashi {X₁ X₂ Y₁ Y₂ : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
    [Nonempty X₁] [Nonempty X₂] [Nonempty Y₁] [Nonempty Y₂]
    (W : FiniteInterferenceChannel X₁ X₂ Y₁ Y₂) :
    Interference.hanKobayashi W ⊆ Interference.capacityRegion W := by
  sorry

/-- Independently tracked cut set converse. -/
@[capacity_problem "general-two-user-interference-channel", capacity_claim "cut-set-converse" 1,
  capacity_statement, capacity_solved]
theorem interferenceCutSet {X₁ X₂ Y₁ Y₂ : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
    [Nonempty X₁] [Nonempty X₂] [Nonempty Y₁] [Nonempty Y₂]
    (W : FiniteInterferenceChannel X₁ X₂ Y₁ Y₂) :
    Interference.capacityRegion W ⊆ Interference.cutSet W := by
  sorry

end CapacityAtlas.Claims
