/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.Optimization
import Mathlib.Analysis.LocallyConvex.Separation

open scoped BigOperators

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx : ℕ} {rx : Fin K → ℕ}

lemma dual_apply_eq_sum (f : (Fin K → ℝ) →L[ℝ] ℝ) (x : Fin K → ℝ) :
    f x = ∑ i, f (Pi.single i 1) * x i := by
  have hx : x = ∑ i, x i • Pi.single i 1 := by
    simp_rw [← Pi.single_smul, smul_eq_mul, mul_one]
    exact (Finset.univ_sum_single x).symm
  nth_rw 1 [hx]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  change x i * f (Pi.single i 1) = f (Pi.single i 1) * x i
  ring

theorem exists_nonneg_weight_separating_region
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    {P : ℝ} {R : Fin K → ℝ} (hR : ∀ i, 0 ≤ R i) (hout : R ∉ region H N P) :
    ∃ w : Fin K → ℝ, (∀ i, 0 ≤ w i) ∧ ∀ S ∈ region H N P,
      (∑ i, w i * S i) < ∑ i, w i * R i := by
  obtain ⟨f, u, hregion, htarget⟩ := geometric_hahn_banach_closed_point
    (convex_region H N P) (isClosed_region H N P) hout
  let a := fun i ↦ f (Pi.single i 1)
  let w := fun i ↦ max (a i) 0
  refine ⟨w, fun i ↦ le_max_right _ _, fun S hS ↦ ?_⟩
  let t := fun i ↦ if 0 ≤ a i then (1 : ℝ) else 0
  have ht0 : ∀ i, 0 ≤ t i := fun i ↦ by dsimp [t]; split_ifs <;> norm_num
  have ht1 : ∀ i, t i ≤ 1 := fun i ↦ by dsimp [t]; split_ifs <;> norm_num
  have hclip := coordinate_mul_mem_region H N ht0 ht1 hS
  have hvalue : f (fun i ↦ t i * S i) = ∑ i, w i * S i := by
    rw [dual_apply_eq_sum]
    apply Finset.sum_congr rfl
    intro i _
    change a i * (t i * S i) = w i * S i
    by_cases ha : 0 ≤ a i
    · simp [t, w, ha]
    · simp [t, w, ha, max_eq_right (le_of_not_ge ha)]
  have htarget_le : f R ≤ ∑ i, w i * R i := by
    rw [dual_apply_eq_sum]
    exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (le_max_left _ _) (hR i)
  rw [← hvalue]
  exact (hregion _ hclip).trans (htarget.trans_le htarget_le)

/-- Membership is equivalent to all nonnegative weighted DPC bounds. -/
theorem mem_region_iff_weighted_bounds
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) {P : ℝ} (hP : 0 ≤ P) {R : Fin K → ℝ} :
    R ∈ region H N P ↔ (∀ i, 0 ≤ R i) ∧ ∀ w : Fin K → ℝ, (∀ i, 0 ≤ w i) →
      ∃ Q, AllocationAdmissible P Q ∧ ∃ π, (∑ i, w i * R i) ≤ weightedDpcRate w H N Q π := by
  constructor
  · intro hR
    refine ⟨region_nonneg H N hR, fun w hw ↦ ?_⟩
    obtain ⟨Q, hQ, π, _, hmax⟩ := exists_region_weighted_max w hw H N hN hP
    refine ⟨Q, hQ, π, ?_⟩
    simpa only [weightedRate_dpcCorner] using hmax R hR
  · rintro ⟨hR, hbound⟩
    by_contra hout
    obtain ⟨w, hw, hsep⟩ := exists_nonneg_weight_separating_region H N hR hout
    obtain ⟨Q, hQ, π, hweight⟩ := hbound w hw
    have hcorner : dpcCorner H N Q π ∈ region H N P :=
      subset_closure (subset_convexHull ℝ _ (dpcCorner_mem_rawRegion H N hN Q hQ π))
    have h := hsep _ hcorner
    rw [weightedRate_dpcCorner] at h
    exact h.not_ge hweight

end CapacityAtlas.Gaussian.MIMOBroadcast
