/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.AchievabilityClosure
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.LayeredAchievability

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx : ℕ} {rx : Fin K → ℕ}

/-- The full DPC region is operationally achievable under the shared total power constraint. -/
theorem region_subset_capacityRegion
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) {P : ℝ} (hP : 0 ≤ P) :
    region H N P ⊆ capacityRegion H N P := by
  apply region_subset_capacityRegion_of_strict_dpc_achievable H N hN hP
  intro hK _ Q hQ π R hR hstrict
  exact strict_dpc_mem_capacityRegion hK H N Q hQ.1 hN π hQ.2 R hR hstrict

end CapacityAtlas.Gaussian.MIMOBroadcast
