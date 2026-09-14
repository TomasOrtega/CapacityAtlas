/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.GaussianWiretap

namespace CapacityAtlas.Claims

/-- Degraded Gaussian strong-secrecy capacity with private finite randomization. -/
@[capacity_problem "gaussian-wiretap-channel", capacity_claim "operational-capacity" 1,
  capacity_statement, capacity_solved]
theorem gaussianWiretap (P N₁ N₂ : ℝ) (hP : 0 ≤ P) (hN₁ : 0 < N₁) (hN : N₁ ≤ N₂) :
    Gaussian.wiretapCapacity P N₁ N₂ =
      Gaussian.awgnFormula P N₁ - Gaussian.awgnFormula P N₂ := by
  sorry

end CapacityAtlas.Claims
