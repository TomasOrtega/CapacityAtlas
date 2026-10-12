/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.CovarianceConstraint
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.RegionProperties
import Mathlib.Topology.Order.Compact

open scoped BigOperators

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx : ℕ} {rx : Fin K → ℕ}

theorem continuousOn_dpcRate
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) (π : Equiv.Perm (Fin K)) (k : Fin K) :
    ContinuousOn (fun Q ↦ dpcRate H N Q π k) {Q | ∀ i, (Q i).PosSemidef} := by
  intro Q hQ
  unfold dpcRate
  apply continuousWithinAt_const.mul
  apply ContinuousWithinAt.logb
  · apply ContinuousWithinAt.div
    · have : Continuous (fun Q ↦ Matrix.det (receivedCovariance (H (π k)) (N (π k))
          (prefixCovariance Q π k + Q (π k)))) := by
        unfold receivedCovariance prefixCovariance
        fun_prop
      exact this.continuousWithinAt
    · have : Continuous (fun Q ↦ Matrix.det (receivedCovariance (H (π k)) (N (π k))
          (prefixCovariance Q π k))) := by
        unfold receivedCovariance prefixCovariance
        fun_prop
      exact this.continuousWithinAt
    · exact (dpcRate_denominator_pos H N Q hN hQ π k).ne'
  · exact (div_pos (dpcRate_numerator_pos H N Q hN hQ π k)
      (dpcRate_denominator_pos H N Q hN hQ π k)).ne'

noncomputable def weightedDpcRate (w : Fin K → ℝ)
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (π : Equiv.Perm (Fin K)) : ℝ :=
  ∑ k, w (π k) * dpcRate H N Q π k

theorem continuousOn_weightedDpcRate (w : Fin K → ℝ)
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) (π : Equiv.Perm (Fin K)) (P : ℝ) :
    ContinuousOn (fun Q ↦ weightedDpcRate w H N Q π) {Q | AllocationAdmissible P Q} := by
  apply continuousOn_finsetSum
  intro k _
  exact continuousOn_const.mul ((continuousOn_dpcRate H N hN π k).mono fun _ hQ ↦ hQ.1)

theorem exists_weightedDpcRate_max_for_order (w : Fin K → ℝ)
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) (π : Equiv.Perm (Fin K)) {P : ℝ} (hP : 0 ≤ P) :
    ∃ Q, AllocationAdmissible P Q ∧ ∀ Q', AllocationAdmissible P Q' →
      weightedDpcRate w H N Q' π ≤ weightedDpcRate w H N Q π := by
  exact (isCompact_allocationAdmissible P).exists_isMaxOn
    ⟨0, allocationAdmissible_zero hP⟩ (continuousOn_weightedDpcRate w H N hN π P)

theorem exists_weightedDpcRate_max (w : Fin K → ℝ)
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) {P : ℝ} (hP : 0 ≤ P) :
    ∃ Q, AllocationAdmissible P Q ∧ ∃ π, ∀ Q', AllocationAdmissible P Q' → ∀ π',
      weightedDpcRate w H N Q' π' ≤ weightedDpcRate w H N Q π := by
  classical
  choose Q hQ hmax using fun π ↦ exists_weightedDpcRate_max_for_order w H N hN π hP
  obtain ⟨π, _, hπ⟩ := Finset.exists_max_image Finset.univ
    (fun π ↦ weightedDpcRate w H N (Q π) π)
    ⟨Equiv.refl _, Finset.mem_univ _⟩
  exact ⟨Q π, hQ π, π, fun Q' hQ' π' ↦ (hmax π' Q' hQ').trans (hπ π' (Finset.mem_univ _))⟩

theorem weightedRate_le_of_mem_rawRegion (w : Fin K → ℝ) (hw : ∀ i, 0 ≤ w i)
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    {P b : ℝ} (hbound : ∀ Q, AllocationAdmissible P Q → ∀ π,
      weightedDpcRate w H N Q π ≤ b) {R : Fin K → ℝ} (hR : R ∈ rawRegion H N P) :
    ∑ i, w i * R i ≤ b := by
  obtain ⟨_, Q, hQ, π, hrate⟩ := hR
  calc
    _ = ∑ k, w (π k) * R (π k) := (Equiv.sum_comp π (fun i ↦ w i * R i)).symm
    _ ≤ weightedDpcRate w H N Q π :=
      Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left (hrate k) (hw (π k))
    _ ≤ b := hbound Q hQ π

theorem weightedRate_le_of_mem_region (w : Fin K → ℝ) (hw : ∀ i, 0 ≤ w i)
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    {P b : ℝ} (hbound : ∀ Q, AllocationAdmissible P Q → ∀ π,
      weightedDpcRate w H N Q π ≤ b) {R : Fin K → ℝ} (hR : R ∈ region H N P) :
    ∑ i, w i * R i ≤ b := by
  have hclosed : IsClosed {R : Fin K → ℝ | ∑ i, w i * R i ≤ b} :=
    isClosed_le (by fun_prop) continuous_const
  have hconvex : Convex ℝ {R : Fin K → ℝ | ∑ i, w i * R i ≤ b} := by
    intro x hx y hy a c ha hc hac
    change ∑ i, w i * (a * x i + c * y i) ≤ b
    have heq : (∑ i, w i * (a * x i + c * y i)) =
        a * (∑ i, w i * x i) + c * (∑ i, w i * y i) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
    rw [heq]
    exact (add_le_add (mul_le_mul_of_nonneg_left hx ha)
      (mul_le_mul_of_nonneg_left hy hc)).trans_eq (by rw [← add_mul, hac, one_mul])
  exact closure_minimal
    (convexHull_min (fun R hR ↦ weightedRate_le_of_mem_rawRegion w hw H N hbound hR) hconvex)
    hclosed hR

noncomputable def dpcCorner
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (π : Equiv.Perm (Fin K)) : Fin K → ℝ :=
  fun i ↦ dpcRate H N Q π (π.symm i)

theorem dpcCorner_mem_rawRegion
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) {P : ℝ}
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (hQ : AllocationAdmissible P Q)
    (π : Equiv.Perm (Fin K)) : dpcCorner H N Q π ∈ rawRegion H N P := by
  refine ⟨fun i ↦ dpcRate_nonneg H N Q hN hQ.1 π (π.symm i), Q, hQ, π, ?_⟩
  intro k
  simp only [dpcCorner, Equiv.symm_apply_apply, le_refl]

theorem weightedRate_dpcCorner (w : Fin K → ℝ)
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (π : Equiv.Perm (Fin K)) :
    (∑ i, w i * dpcCorner H N Q π i) = weightedDpcRate w H N Q π := by
  rw [← Equiv.sum_comp π (fun i ↦ w i * dpcCorner H N Q π i)]
  simp only [dpcCorner, Equiv.symm_apply_apply, weightedDpcRate]

/-- Every nonnegative supporting weight attains its maximum at an actual DPC corner. -/
theorem exists_region_weighted_max (w : Fin K → ℝ) (hw : ∀ i, 0 ≤ w i)
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) {P : ℝ} (hP : 0 ≤ P) :
    ∃ Q, AllocationAdmissible P Q ∧ ∃ π,
      dpcCorner H N Q π ∈ region H N P ∧ ∀ R ∈ region H N P,
        (∑ i, w i * R i) ≤ ∑ i, w i * dpcCorner H N Q π i := by
  obtain ⟨Q, hQ, π, hmax⟩ := exists_weightedDpcRate_max w H N hN hP
  refine ⟨Q, hQ, π, subset_closure (subset_convexHull ℝ _
    (dpcCorner_mem_rawRegion H N hN Q hQ π)), fun R hR ↦ ?_⟩
  rw [weightedRate_dpcCorner]
  exact weightedRate_le_of_mem_region w hw H N hmax hR

theorem isCompact_region
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) {P : ℝ} (hP : 0 ≤ P) : IsCompact (region H N P) := by
  obtain ⟨Q, _, π, _, hmax⟩ := exists_region_weighted_max (fun _ ↦ 1) (fun _ ↦ zero_le_one)
    H N hN hP
  let b := ∑ i, dpcCorner H N Q π i
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : Fin K → ℝ) (fun _ ↦ b))).of_isClosed_subset
    (isClosed_region H N P)
  intro R hR
  refine ⟨fun i ↦ region_nonneg H N hR i, fun i ↦ ?_⟩
  apply (Finset.single_le_sum (fun j _ ↦ region_nonneg H N hR j) (Finset.mem_univ i)).trans
  simpa only [one_mul] using hmax R hR

theorem coordinate_mul_mem_rawRegion
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    {P : ℝ} {t R : Fin K → ℝ} (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1)
    (hR : R ∈ rawRegion H N P) : (fun i ↦ t i * R i) ∈ rawRegion H N P := by
  obtain ⟨hR0, Q, hQ, π, hrate⟩ := hR
  refine ⟨fun i ↦ mul_nonneg (ht0 i) (hR0 i), Q, hQ, π, fun k ↦ ?_⟩
  exact (mul_le_of_le_one_left (hR0 (π k)) (ht1 (π k))).trans (hrate k)

theorem coordinate_mul_mem_region
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    {P : ℝ} {t R : Fin K → ℝ} (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1)
    (hR : R ∈ region H N P) : (fun i ↦ t i * R i) ∈ region H N P := by
  have hclosed : IsClosed {R : Fin K → ℝ | (fun i ↦ t i * R i) ∈ region H N P} :=
    (isClosed_region H N P).preimage (by fun_prop)
  have hconvex : Convex ℝ {R : Fin K → ℝ | (fun i ↦ t i * R i) ∈ region H N P} := by
    intro x hx y hy a b ha hb hab
    change (fun i ↦ t i * (a * x i + b * y i)) ∈ region H N P
    have heq : (fun i ↦ t i * (a * x i + b * y i)) =
        a • (fun i ↦ t i * x i) + b • (fun i ↦ t i * y i) := by
      ext i
      change t i * (a * x i + b * y i) = a * (t i * x i) + b * (t i * y i)
      ring
    rw [heq]
    exact convex_region H N P hx hy ha hb hab
  have hsubset : rawRegion H N P ⊆
      {R : Fin K → ℝ | (fun i ↦ t i * R i) ∈ region H N P} := by
    intro R hraw
    exact subset_closure (subset_convexHull ℝ (rawRegion H N P)
      (coordinate_mul_mem_rawRegion H N ht0 ht1 hraw))
  exact closure_minimal (convexHull_min hsubset hconvex) hclosed hR

theorem mem_region_of_nonneg_le
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    {P : ℝ} {R R' : Fin K → ℝ} (hR : R ∈ region H N P)
    (hR' : ∀ i, 0 ≤ R' i) (hle : ∀ i, R' i ≤ R i) : R' ∈ region H N P := by
  let t := fun i ↦ if R i = 0 then 0 else R' i / R i
  have ht0 : ∀ i, 0 ≤ t i := fun i ↦ by
    dsimp [t]
    split_ifs
    · exact le_rfl
    · exact div_nonneg (hR' i) (region_nonneg H N hR i)
  have ht1 : ∀ i, t i ≤ 1 := fun i ↦ by
    dsimp [t]
    split_ifs with hzero
    · exact zero_le_one
    · exact (div_le_one (lt_of_le_of_ne (region_nonneg H N hR i) (Ne.symm hzero))).mpr (hle i)
  have heq : (fun i ↦ t i * R i) = R' := by
    funext i
    dsimp [t]
    split_ifs with hzero
    · have hz : R' i = 0 := le_antisymm ((hle i).trans_eq hzero) (hR' i)
      simp [hz]
    · exact div_mul_cancel₀ (R' i) hzero
  simpa only [heq] using coordinate_mul_mem_region H N ht0 ht1 hR

end CapacityAtlas.Gaussian.MIMOBroadcast
