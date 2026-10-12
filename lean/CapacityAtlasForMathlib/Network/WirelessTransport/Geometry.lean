/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

open scoped BigOperators
open MeasureTheory Metric

namespace CapacityAtlas.WirelessTransport

abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- Packing disjoint planar disks bounds the sum of their radii. -/
theorem sum_radii_le {I : Type*} [Fintype I] (c : I → Point) (r : I → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hr : ∀ i, 0 ≤ r i)
    (hcontained : ∀ i, ‖c i‖ + r i ≤ B)
    (hdisjoint : Pairwise fun i j => Disjoint (ball (c i) (r i)) (ball (c j) (r j))) :
    ∑ i, r i ≤ B * Real.sqrt (Fintype.card I) := by
  classical
  have hsubset : (⋃ i, ball (c i) (r i)) ⊆ ball (0 : Point) B := by
    refine Set.iUnion_subset fun i x hx => ?_
    rw [mem_ball, dist_zero_right]
    have hx' := mem_ball.mp hx
    have htri : ‖x‖ ≤ dist x (c i) + ‖c i‖ := by
      simpa using dist_triangle x (c i) (0 : Point)
    linarith [hcontained i]
  have hmeasure : ∑ i, volume.real (ball (c i) (r i)) ≤
      volume.real (ball (0 : Point) B) := by
    calc
      ∑ i, volume.real (ball (c i) (r i)) =
          volume.real (⋃ i, ball (c i) (r i)) := by
        simpa using (measureReal_biUnion_finset (μ := volume) (s := Finset.univ)
          (fun i _ j _ hij => hdisjoint hij) (fun _ _ => measurableSet_ball)).symm
      _ ≤ volume.real (ball (0 : Point) B) := measureReal_mono hsubset
  have harea : ∑ i, r i ^ 2 * Real.pi ≤ B ^ 2 * Real.pi := by
    simpa [Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal, hr, hB, Real.pi_pos.le] using hmeasure
  have hsquare : ∑ i, r i ^ 2 ≤ B ^ 2 := by
    rw [← Finset.sum_mul] at harea
    nlinarith [Real.pi_pos]
  have hsqrt : Real.sqrt (∑ i, r i ^ 2) ≤ B := by
    exact (Real.sqrt_le_iff).2 ⟨hB, hsquare⟩
  calc
    ∑ i, r i ≤ Real.sqrt (∑ i, r i ^ 2) * Real.sqrt (Fintype.card I) := by
      simpa using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ r (fun _ => (1 : ℝ))
    _ ≤ B * Real.sqrt (Fintype.card I) := mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)

/-- The protocol exclusion inequalities separate receiver guard disks. -/
theorem guard_disks_disjoint {I : Type*} (tx rx : I → Point) (Δ : ℝ)
    (hprotocol : ∀ i j, i ≠ j → (1 + Δ) * dist (tx i) (rx i) ≤ dist (tx j) (rx i)) :
    Pairwise fun i j => Disjoint (ball (rx i) (Δ / 2 * dist (tx i) (rx i)))
      (ball (rx j) (Δ / 2 * dist (tx j) (rx j))) := by
  intro i j hij
  apply ball_disjoint_ball
  have h₁ := (hprotocol i j hij).trans (dist_triangle (tx j) (rx j) (rx i))
  have h₂ := (hprotocol j i hij.symm).trans (dist_triangle (tx i) (rx i) (rx j))
  rw [dist_comm (rx j) (rx i)] at h₁
  linarith

/-- A simultaneous protocol-model schedule has at most square-root total hop length. -/
theorem sum_linkLength_le {I : Type*} [Fintype I] (tx rx : I → Point) (R Δ : ℝ)
    (hR : 0 ≤ R) (hΔ : 0 < Δ) (htx : ∀ i, ‖tx i‖ ≤ R) (hrx : ∀ i, ‖rx i‖ ≤ R)
    (hprotocol : ∀ i j, i ≠ j → (1 + Δ) * dist (tx i) (rx i) ≤ dist (tx j) (rx i)) :
    ∑ i, dist (tx i) (rx i) ≤ (2 * (1 + Δ) * R / Δ) * Real.sqrt (Fintype.card I) := by
  have hlink : ∀ i, dist (tx i) (rx i) ≤ 2 * R := by
    intro i
    exact (dist_le_norm_add_norm _ _).trans (by linarith [htx i, hrx i])
  have hpacking := sum_radii_le rx (fun i => Δ / 2 * dist (tx i) (rx i))
    (R * (1 + Δ)) (by positivity) (fun _ => by positivity)
    (fun i => by nlinarith [hrx i, hlink i]) (guard_disks_disjoint tx rx Δ hprotocol)
  rw [← Finset.mul_sum] at hpacking
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hΔ).2
  nlinarith [hpacking]

end CapacityAtlas.WirelessTransport
