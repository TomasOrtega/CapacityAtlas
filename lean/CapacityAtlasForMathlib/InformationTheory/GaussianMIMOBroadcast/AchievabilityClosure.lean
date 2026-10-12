/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.Approximation
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.Boundary
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.TimeSharing

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx : ℕ} {rx : Fin K → ℕ}

theorem mem_capacityRegion_no_receivers {rx : Fin 0 → ℕ}
    (H : (i : Fin 0) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin 0) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    {P : ℝ} (hP : 0 ≤ P) (R : Fin 0 → ℝ) : R ∈ capacityRegion H N P := by
  have hR : R = 0 := by funext i; exact Fin.elim0 i
  rw [hR]
  exact zero_mem_capacityRegion H N hP

theorem capacityRegion_eq_region_no_transmit_antennas
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin 0) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) {P : ℝ} (hP : 0 ≤ P) :
    capacityRegion H N P = region H N P := by
  have hH : H = 0 := by funext i a b; exact Fin.elim0 b
  rw [hH]
  exact capacityRegion_eq_region_zero_channel N hN hP

/-- Strict interior coding suffices for the full closed convex DPC region. -/
theorem region_subset_capacityRegion_of_strict_dpc_achievable
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) {P : ℝ} (hP : 0 ≤ P)
    (hstrict : 0 < K → 0 < tx →
      ∀ Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ, InteriorAllocationAdmissible P Q →
      ∀ π : Equiv.Perm (Fin K), ∀ R : Fin K → ℝ, (∀ i, 0 ≤ R i) →
        (∀ k, R (π k) = 0 ∨ R (π k) < dpcRate H N Q π k) → R ∈ capacityRegion H N P) :
    region H N P ⊆ capacityRegion H N P := by
  by_cases hK : K = 0
  · subst K
    exact fun R _ ↦ mem_capacityRegion_no_receivers H N hP R
  by_cases htx : tx = 0
  · subst tx
    rw [capacityRegion_eq_region_no_transmit_antennas H N hN hP]
  by_cases hPzero : P = 0
  · subst P
    rw [capacityRegion_eq_region_zero_power H N hN]
  apply region_subset_of_strictInteriorRawRegion_subset H N hN
    (lt_of_le_of_ne hP (Ne.symm hPzero)) (isClosed_capacityRegion H N P)
    (convex_capacityRegion H N P)
  rintro R ⟨hR, Q, hQ, π, hrate⟩
  exact hstrict (Nat.pos_of_ne_zero hK) (Nat.pos_of_ne_zero htx) Q hQ π R hR hrate

end CapacityAtlas.Gaussian.MIMOBroadcast
