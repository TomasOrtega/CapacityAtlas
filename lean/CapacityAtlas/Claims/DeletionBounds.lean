/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.DeletionOperational

namespace CapacityAtlas.Claims

/-- Published deletion bounds in bits per INPUT bit, with the high-deletion restriction explicit. -/
@[capacity_problem "binary-deletion-channel", capacity_claim "published-capacity-bounds" 1,
  capacity_statement, capacity_solved]
theorem deletionBounds (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) :
    (1221 / 10000 : ℝ) * (1 - d) < Deletion.capacity d ∧
      ((16 / 25 : ℝ) ≤ d → Deletion.capacity d ≤ (1789 / 5000 : ℝ) * (1 - d)) := by
  sorry

/-- Independently tracked run length achievability. -/
@[capacity_problem "binary-deletion-channel", capacity_claim "run-length-achievability" 1,
  capacity_statement, capacity_solved]
theorem deletionRunLength (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) :
    (1221 / 10000 : ℝ) * (1 - d) < Deletion.capacity d := by
  sorry

/-- Independently tracked high deletion converse. -/
@[capacity_problem "binary-deletion-channel", capacity_claim "high-deletion-converse" 1,
  capacity_statement, capacity_solved]
theorem deletionHighConverse (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) :
    ((16 / 25 : ℝ) ≤ d → Deletion.capacity d ≤ (1789 / 5000 : ℝ) * (1 - d)) := by
  sorry

end CapacityAtlas.Claims
