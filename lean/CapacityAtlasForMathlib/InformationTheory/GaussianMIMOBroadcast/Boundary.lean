/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.NoInformation
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.RegionProperties

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx : ℕ} {rx : Fin K → ℕ}

/-- The operational and dirty-paper regions coincide at zero transmit power. -/
theorem capacityRegion_eq_region_zero_power
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) : capacityRegion H N 0 = region H N 0 := by
  rw [capacityRegion_zero_power, region_zero_power H N hN]

/-- Zero channel gains preclude information transmission at any nonnegative power. -/
theorem capacityRegion_eq_region_zero_channel
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) {P : ℝ} (hP : 0 ≤ P) :
    capacityRegion (0 : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ) N P =
      region (tx := tx) 0 N P := by
  rw [capacityRegion_zero_channel N hP, region_zero_channel N hN hP]

end CapacityAtlas.Gaussian.MIMOBroadcast
