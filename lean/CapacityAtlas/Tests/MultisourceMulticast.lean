/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Network.Multisource.Capacity

namespace CapacityAtlas.Tests

open Multisource Multisource.Network

private def sharedBottleneck : Multisource.Network 4 3 2 where
  source := ![0, 1, 2]
  target := ![2, 2, 3]
  increasing e := by fin_cases e <;> decide
  sourceNode := ![0, 1]
  linkRate := fun _ ↦ 1
  linkRate_nonneg _ := zero_le_one
  sinks := {3}
  sinks_nonempty := by simp

@[capacity_test]
theorem multisource_bottleneck_sum_rate {r : Fin 2 → ℝ}
    (hr : r ∈ sharedBottleneck.capacityRegion) : r 0 + r 1 ≤ 1 := by
  have hc := sharedBottleneck.capacityRegion_subset_cutRegion hr
  have hh := hc.2 3 (by simp [sharedBottleneck]) {0, 1, 2} (by decide)
  simp only [cutDemand, cutRate, Fin.sum_univ_succ] at hh
  simpa [sharedBottleneck] using hh

private theorem bottleneck_cut_region (r : Fin 2 → ℝ) :
    r ∈ sharedBottleneck.cutRegion ↔ 0 ≤ r 0 ∧ 0 ≤ r 1 ∧ r 0 + r 1 ≤ 1 := by
  constructor
  · intro hr
    refine ⟨hr.1 0, hr.1 1, ?_⟩
    have hh := hr.2 3 (by simp [sharedBottleneck]) {0, 1, 2} (by decide)
    simp only [cutDemand, cutRate, Fin.sum_univ_succ] at hh
    simpa [sharedBottleneck] using hh
  · rintro ⟨h0, h1, hsum⟩
    refine ⟨fun i ↦ ?_, fun v hv cut hcut ↦ ?_⟩
    · fin_cases i <;> assumption
    · have hv3 : v = 3 := by simpa [sharedBottleneck] using hv
      subst v
      simp only [cutDemand, cutRate, Fin.sum_univ_succ]
      by_cases hc0 : (0 : Fin 4) ∈ cut <;>
        by_cases hc1 : (1 : Fin 4) ∈ cut <;>
        by_cases hc2 : (2 : Fin 4) ∈ cut <;>
        simp [sharedBottleneck, hc0, hc1, hc2, hcut] <;> linarith

@[capacity_test]
theorem multisource_bottleneck_capacity_region (r : Fin 2 → ℝ) :
    r ∈ sharedBottleneck.capacityRegion ↔ 0 ≤ r 0 ∧ 0 ≤ r 1 ∧ r 0 + r 1 ≤ 1 := by
  rw [sharedBottleneck.capacityRegion_eq_cutRegion]
  exact bottleneck_cut_region r

private def localSource : Multisource.Network 1 0 1 where
  source := Fin.elim0
  target := Fin.elim0
  increasing e := Fin.elim0 e
  sourceNode := fun _ ↦ 0
  linkRate := Fin.elim0
  linkRate_nonneg e := Fin.elim0 e
  sinks := {0}
  sinks_nonempty := by simp

@[capacity_test]
theorem multisource_local_source_capacity (r : ℝ) (hr : 0 ≤ r) :
    (fun _ ↦ r) ∈ localSource.capacityRegion := by
  rw [localSource.capacityRegion_eq_cutRegion]
  refine ⟨fun _ ↦ hr, fun v hv cut hcut ↦ ?_⟩
  have hv0 : v = 0 := Subsingleton.elim _ _
  subst v
  simp [cutDemand, cutRate, localSource, hcut]

end CapacityAtlas.Tests
