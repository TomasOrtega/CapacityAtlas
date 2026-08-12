/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteChannelCapacity

namespace CapacityAtlas

abbrev RatePair := ℝ × ℝ

/-- An operational scalar-capacity interface, separated from a channel's physical model. -/
@[capacity_shared_api]
structure ScalarOperationalTheory (Model : Type*) where
  achievable : Model → ℝ → Prop

namespace ScalarOperationalTheory

@[capacity_shared_api]
noncomputable def capacity {Model : Type*} (theory : ScalarOperationalTheory Model)
    (model : Model) : ℝ :=
  sSup {rate | theory.achievable model rate}

end ScalarOperationalTheory

/-- An operational two-rate capacity-region interface. -/
@[capacity_shared_api]
structure RegionOperationalTheory (Model : Type*) where
  achievable : Model → RatePair → Prop

namespace RegionOperationalTheory

@[capacity_shared_api]
def capacityRegion {Model : Type*} (theory : RegionOperationalTheory Model)
    (model : Model) : Set RatePair :=
  {rate | theory.achievable model rate}

end RegionOperationalTheory

end CapacityAtlas
