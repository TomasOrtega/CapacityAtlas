/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.OrderedConverse
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.Relabel
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.PositiveSupportingWeights
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.Boundary

open scoped BigOperators

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {m tx : ℕ} {rx : Fin (m + 1) → ℕ}

/-- Every positive support weight is bounded by an actual Gaussian dirty-paper allocation. -/
theorem exists_capacity_weighted_bound
    (H : (i : Fin (m + 1)) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin (m + 1)) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) (htx : 0 < tx)
    (w : Fin (m + 1) → ℝ) (hw : ∀ i, 0 < w i)
    {P : ℝ} (hP : 0 < P) {R : Fin (m + 1) → ℝ} (hR : R ∈ capacityRegion H N P) :
    ∃ Q, AllocationAdmissible P Q ∧ ∃ π,
      (∑ i, w i * R i) ≤ weightedDpcRate w H N Q π := by
  apply exists_weightedDpcRate_bound_of_sorted w H N
  intro σ hmono
  exact exists_capacity_weighted_bound_ordered (fun i ↦ H (σ i)) (fun i ↦ N (σ i))
    (fun i ↦ hN (σ i)) htx (fun i ↦ w (σ i)) (fun i ↦ hw (σ i)) hmono hP
    (mem_capacityRegion_relabel H N σ hR)

/-- The operational region satisfies every supporting inequality of the Gaussian region. -/
theorem capacityRegion_subset_region_positive_power
    (H : (i : Fin (m + 1)) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin (m + 1)) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) (htx : 0 < tx) {P : ℝ} (hP : 0 < P) :
    capacityRegion H N P ⊆ region H N P := by
  intro R hR
  apply (mem_region_iff_positive_weighted_bounds H N hN hP.le).mpr
  exact ⟨capacityRegion_nonneg hR,
    fun w hw ↦ exists_capacity_weighted_bound H N hN htx w hw hP hR⟩

variable {K : ℕ} {rx : Fin K → ℕ}

/-- Gaussian MIMO broadcast converse under the native average-power and joint-error model. -/
theorem capacityRegion_subset_region
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) (hK : 0 < K) (htx : 0 < tx) {P : ℝ} (hP : 0 ≤ P) :
    capacityRegion H N P ⊆ region H N P := by
  rcases eq_or_lt_of_le hP with hzero | hpositive
  · subst P
    exact (capacityRegion_eq_region_zero_power H N hN).subset
  · cases K with
    | zero => omega
    | succ m => exact capacityRegion_subset_region_positive_power H N hN htx hpositive

end CapacityAtlas.Gaussian.MIMOBroadcast
