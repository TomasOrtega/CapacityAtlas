/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.Capacity

open MeasureTheory Filter
open scoped Topology

namespace CapacityAtlas.Claims

@[capacity_problem "k-user-gaussian-interference-channel",
  capacity_claim "sum-degrees-of-freedom" 1, capacity_statement, capacity_solved,
  capacity_formal_proof]
theorem gaussianInterferenceDegreesOfFreedom (μ : Measure ℂ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] {K : ℕ} (hK : 2 ≤ K) {hmin hmax : ℝ}
    (hmin_pos : 0 < hmin) (hmax_nonneg : 0 ≤ hmax)
    (hfading : ∀ᵐ h ∂μ, hmin ≤ ‖h‖ ∧ ‖h‖ ≤ hmax) :
    Tendsto (fun P : ℝ => Gaussian.Interference.sumCapacity μ K P / Real.logb 2 P)
      atTop (𝓝 ((K : ℝ) / 2)) :=
  Gaussian.Interference.sum_degrees_of_freedom μ hK hmin_pos hmax_nonneg hfading

end CapacityAtlas.Claims
