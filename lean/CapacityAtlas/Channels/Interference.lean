/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Network.FiniteInterferenceChannel

namespace CapacityAtlas.Channel

open CapacityAtlas

@[capacity_problem "strong-interference-two-user-dmc", capacity_statement]
def strongInterferenceCapacityStatement {X₁ X₂ Y₁ Y₂ : Type*}
    [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
    (theory : RegionOperationalTheory (FiniteInterferenceChannel X₁ X₂ Y₁ Y₂))
    (macIntersectionRegion : FiniteInterferenceChannel X₁ X₂ Y₁ Y₂ → Set RatePair)
    (channel : FiniteInterferenceChannel X₁ X₂ Y₁ Y₂) : Prop :=
  channel.IsStrongInterference →
    theory.capacityRegion channel = macIntersectionRegion channel

end CapacityAtlas.Channel
