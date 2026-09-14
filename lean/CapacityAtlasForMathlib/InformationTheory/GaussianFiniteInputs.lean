/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianOperational
import CapacityAtlasForMathlib.InformationTheory.FiniteDistribution

open MeasureTheory
open scoped BigOperators

namespace CapacityAtlas.Gaussian

/-- A genuine finite-support Borel input measure. -/
noncomputable def finiteInput {k : ℕ} (p : FiniteDistribution (Fin k))
    (location : Fin k → ℝ) : Measure ℝ :=
  ∑ i, ENNReal.ofReal (p i) • Measure.dirac (location i)

end CapacityAtlas.Gaussian
