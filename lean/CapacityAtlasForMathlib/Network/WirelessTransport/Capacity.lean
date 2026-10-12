/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Network.WirelessTransport.Operations
import CapacityAtlasForMathlib.Network.WirelessTransport.OneHop
import CapacityAtlasForMathlib.Network.WirelessTransport.Grid
import CapacityAtlasForMathlib.Network.WirelessTransport.Rounding

namespace CapacityAtlas.WirelessTransport

theorem capacity_lower {n : ℕ} {R Δ W : ℝ}
    (hn : 4 ≤ n) (hR : 0 < R) (hΔ : 0 < Δ) (hW : 0 ≤ W) :
    W * R * Real.sqrt n / (32 * (1 + Δ)) ≤ capacity n R Δ W := by
  obtain ⟨m, hm, hcount, hroot⟩ := exists_grid_size hn
  have hc : 2 * Fintype.card (GridIndex m) ≤ n := by simpa using hcount
  have ha := oneHop_achievable (GridIndex m) (gridTx R Δ m) (gridRx R Δ m) R Δ W hc hW
    (gridTx_norm_le hR hm) (gridRx_norm_le hR hΔ hm)
    (fun _ _ hij => grid_protocol hR hΔ hm hij)
  rw [grid_total_length hR hΔ hm] at ha
  have hlower : W * R * Real.sqrt n / (32 * (1 + Δ)) ≤
      W * (R * (m : ℝ) / (8 * (1 + Δ))) := by
    have hden : 0 < 32 * (1 + Δ) := by positivity
    apply (div_le_iff₀ hden).2
    have he : W * (R * (m : ℝ) / (8 * (1 + Δ))) * (32 * (1 + Δ)) =
        W * R * (4 * (m : ℝ)) := by
      have hd : 1 + Δ ≠ 0 := by positivity
      field_simp
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hroot (mul_nonneg hW hR.le)
  exact hlower.trans (ha.le_capacity hR.le hΔ hW)

/-- Nonsharp constants give matching order bounds for every node count at least four. -/
theorem capacity_bounds {n : ℕ} {R Δ W : ℝ}
    (hn : 4 ≤ n) (hR : 0 < R) (hΔ : 0 < Δ) (hW : 0 ≤ W) :
    W * R * Real.sqrt n / (32 * (1 + Δ)) ≤ capacity n R Δ W ∧
      capacity n R Δ W ≤ W * (2 * (1 + Δ) * R / Δ) * Real.sqrt n :=
  ⟨capacity_lower hn hR hΔ hW, capacity_le hR.le hΔ hW⟩

end CapacityAtlas.WirelessTransport
