/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcastRegion
import CapacityAtlasUtil.Metadata
import Mathlib.Algebra.Order.Star.Real

open scoped BigOperators

namespace CapacityAtlas.Tests

open Gaussian.MIMOBroadcast

private def scalarBroadcastH (_ : Fin 2) : Matrix (Fin 1) (Fin 1) ℝ := 1

private def scalarBroadcastN (i : Fin 2) : Matrix (Fin 1) (Fin 1) ℝ :=
  fun _ _ ↦ if i = 0 then 1 else 3

private def scalarBroadcastQ (i : Fin 2) : Matrix (Fin 1) (Fin 1) ℝ :=
  fun _ _ ↦ if i = 0 then 1 else 4

/-- The first layer sees noise alone; the second sees the first layer as interference. -/
@[capacity_test]
theorem mimoBroadcast_scalar_prefix_rates :
    dpcRate scalarBroadcastH scalarBroadcastN scalarBroadcastQ (Equiv.refl _) 0 =
      (1 / 2 : ℝ) ∧
    dpcRate scalarBroadcastH scalarBroadcastN scalarBroadcastQ (Equiv.refl _) 1 =
      (1 / 2 : ℝ) := by
  norm_num [dpcRate, receivedCovariance, prefixCovariance, scalarBroadcastH,
    scalarBroadcastN, scalarBroadcastQ, Finset.sum_filter, Fin.sum_univ_succ,
    Matrix.add_apply, Real.logb]

/-- Swapping the order swaps receiver noises as well as allocated layers. -/
@[capacity_test]
theorem mimoBroadcast_swapped_receiver_rates :
    dpcRate scalarBroadcastH scalarBroadcastN scalarBroadcastQ (Equiv.swap 0 1) 0 =
      (1 / 2 : ℝ) * Real.logb 2 (7 / 3) ∧
    dpcRate scalarBroadcastH scalarBroadcastN scalarBroadcastQ (Equiv.swap 0 1) 1 =
      (1 / 2 : ℝ) * Real.logb 2 (6 / 5) := by
  norm_num [dpcRate, receivedCovariance, prefixCovariance, scalarBroadcastH,
    scalarBroadcastN, scalarBroadcastQ, Finset.sum_filter, Fin.sum_univ_succ,
    Matrix.add_apply, Equiv.swap_apply_def]

/-- Two users each occupying two unit-power antennas consume four units in total. -/
@[capacity_test]
theorem mimoBroadcast_shared_trace_budget :
    AllocationAdmissible 4 (fun _ : Fin 2 ↦ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
      ¬AllocationAdmissible 2 (fun _ : Fin 2 ↦ (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  constructor
  · constructor
    · exact fun _ ↦ Matrix.PosSemidef.one
    · norm_num [Matrix.trace, Fin.sum_univ_succ]
  · intro h
    have hbudget := h.2
    norm_num [Matrix.trace, Fin.sum_univ_succ] at hbudget

end CapacityAtlas.Tests
