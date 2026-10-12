/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil
import CapacityAtlasForMathlib.Network.WirelessTransport.Capacity

namespace CapacityAtlas.Claims

@[capacity_problem "wireless-network-transport-capacity", capacity_statement,
  capacity_formal_proof, capacity_solved, capacity_claim "square-root-bounds" 1]
theorem wirelessTransportBounds {n : ℕ} {R Δ W : ℝ}
    (hn : 4 ≤ n) (hR : 0 < R) (hΔ : 0 < Δ) (hW : 0 ≤ W) :
    W * R * Real.sqrt n / (32 * (1 + Δ)) ≤ WirelessTransport.capacity n R Δ W ∧
      WirelessTransport.capacity n R Δ W ≤
        W * (2 * (1 + Δ) * R / Δ) * Real.sqrt n :=
  WirelessTransport.capacity_bounds hn hR hΔ hW

end CapacityAtlas.Claims
