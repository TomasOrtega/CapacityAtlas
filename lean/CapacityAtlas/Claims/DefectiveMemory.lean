/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.NoncausalState

namespace CapacityAtlas.Claims

/-- Noncausal knowledge of the entire iid stuck-at pattern gives capacity 1-delta. -/
@[capacity_problem "binary-memory-with-stuck-defects", capacity_claim "operational-capacity" 1,
  capacity_statement, capacity_solved]
theorem defectiveMemory (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (p : FiniteDistribution NoncausalState.Defect) (hp : NoncausalState.IsDefectLaw δ p) :
    NoncausalState.capacity p NoncausalState.defectChannel = 1 - δ := by
  sorry

end CapacityAtlas.Claims
