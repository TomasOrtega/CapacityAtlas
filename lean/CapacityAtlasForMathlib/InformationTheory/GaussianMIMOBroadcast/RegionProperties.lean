/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcastRegion
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.SchurComplement

open scoped BigOperators

namespace Matrix

open Unitary
open scoped MatrixOrder

theorem PosSemidef.one_le_det_one_add {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) : 1 ≤ (1 + A).det := by
  rw [hA.isHermitian.spectral_theorem,
    ← map_one (conjStarAlgAut ℝ (Matrix n n ℝ) hA.isHermitian.eigenvectorUnitary),
    ← map_add]
  simp only [conjStarAlgAut_apply]
  rw [det_mul_comm, ← Matrix.mul_assoc, Unitary.coe_star_mul_self, one_mul,
    ← diagonal_one, diagonal_add, det_diagonal]
  apply Finset.one_le_prod
  intro i _
  simpa using add_le_add_left (hA.eigenvalues_nonneg i) 1

theorem PosDef.det_le_det_add {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosSemidef) :
    A.det ≤ (A + B).det := by
  obtain ⟨X, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [Matrix.det_add_mul _ _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne')]
  have hX : (X * A⁻¹ * star X).PosSemidef :=
    hA.inv.posSemidef.mul_mul_conjTranspose_same X
  simpa using mul_le_mul_of_nonneg_left hX.one_le_det_one_add hA.det_pos.le

end Matrix

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx : ℕ} {rx : Fin K → ℕ}

theorem allocationAdmissible_zero_iff
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) :
    AllocationAdmissible 0 Q ↔ Q = 0 := by
  constructor
  · intro hQ
    funext i
    apply (hQ.1 i).trace_eq_zero_iff.mp
    apply le_antisymm _ (hQ.1 i).trace_nonneg
    exact (Finset.single_le_sum (fun j _ ↦ (hQ.1 j).trace_nonneg)
      (Finset.mem_univ i)).trans hQ.2
  · rintro rfl
    exact ⟨fun _ ↦ Matrix.PosSemidef.zero, by simp⟩

theorem allocationAdmissible_mono {P P' : ℝ}
    {Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ}
    (hQ : AllocationAdmissible P Q) (hP : P ≤ P') : AllocationAdmissible P' Q :=
  ⟨hQ.1, hQ.2.trans hP⟩

theorem allocationAdmissible_zero {P : ℝ} (hP : 0 ≤ P) :
    AllocationAdmissible P (0 : Fin K → Matrix (Fin tx) (Fin tx) ℝ) :=
  allocationAdmissible_mono ((allocationAdmissible_zero_iff _).2 rfl) hP

theorem dpcRate_zero
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) (π : Equiv.Perm (Fin K)) (k : Fin K) :
    dpcRate H N 0 π k = 0 := by
  simp [dpcRate, prefixCovariance, receivedCovariance, (hN (π k)).det_pos.ne']

theorem dpcRate_nonneg
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (hN : ∀ i, (N i).PosDef) (hQ : ∀ i, (Q i).PosSemidef)
    (π : Equiv.Perm (Fin K)) (k : Fin K) : 0 ≤ dpcRate H N Q π k := by
  have hprefix := prefixCovariance_posSemidef Q hQ π k
  have hsignal : ((H (π k)) * Q (π k) * (H (π k)).transpose).PosSemidef := by
    simpa using (hQ (π k)).mul_mul_conjTranspose_same (H (π k))
  have hdet := (receivedCovariance_posDef (H (π k)) (N (π k))
    (prefixCovariance Q π k) (hN (π k)) hprefix).det_le_det_add hsignal
  have hmono : Matrix.det (receivedCovariance (H (π k)) (N (π k))
        (prefixCovariance Q π k)) ≤
      Matrix.det (receivedCovariance (H (π k)) (N (π k))
        (prefixCovariance Q π k + Q (π k))) := by
    simpa [receivedCovariance, Matrix.mul_add, Matrix.add_mul, add_assoc] using hdet
  exact mul_nonneg (by norm_num) (Real.logb_nonneg (by norm_num)
    ((one_le_div (dpcRate_denominator_pos H N Q hN hQ π k)).2 hmono))

theorem zero_mem_rawRegion
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) {P : ℝ} (hP : 0 ≤ P) :
    (0 : Fin K → ℝ) ∈ rawRegion H N P := by
  refine ⟨fun _ ↦ le_rfl, 0, allocationAdmissible_zero hP, Equiv.refl _, ?_⟩
  intro k
  simp [dpcRate_zero H N hN]

theorem rawRegion_mono
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    {P P' : ℝ} (hP : P ≤ P') : rawRegion H N P ⊆ rawRegion H N P' := by
  rintro R ⟨hR, Q, hQ, hπ⟩
  exact ⟨hR, Q, allocationAdmissible_mono hQ hP, hπ⟩

theorem rawRegion_zero_power
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) : rawRegion H N 0 = {0} := by
  apply Set.Subset.antisymm
  · rintro R ⟨hR, Q, hQ, π, hbound⟩
    have hQzero := (allocationAdmissible_zero_iff Q).1 hQ
    subst Q
    apply Set.mem_singleton_iff.mpr
    funext i
    apply le_antisymm _ (hR i)
    simpa [dpcRate_zero H N hN] using hbound (π.symm i)
  · rintro R rfl
    exact zero_mem_rawRegion H N hN le_rfl

theorem dpcRate_zero_channel
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (hN : ∀ i, (N i).PosDef) (π : Equiv.Perm (Fin K)) (k : Fin K) :
    dpcRate 0 N Q π k = 0 := by
  simp [dpcRate, receivedCovariance, (hN (π k)).det_pos.ne']

theorem rawRegion_zero_channel
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) {P : ℝ} (hP : 0 ≤ P) :
    rawRegion (0 : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ) N P = {0} := by
  apply Set.Subset.antisymm
  · rintro R ⟨hR, Q, _, π, hbound⟩
    apply Set.mem_singleton_iff.mpr
    funext i
    apply le_antisymm _ (hR i)
    simpa [dpcRate_zero_channel N Q hN] using hbound (π.symm i)
  · rintro R rfl
    exact zero_mem_rawRegion 0 N hN hP

theorem zero_mem_region
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) {P : ℝ} (hP : 0 ≤ P) :
    (0 : Fin K → ℝ) ∈ region H N P :=
  subset_closure (subset_convexHull ℝ _ (zero_mem_rawRegion H N hN hP))

theorem region_mono
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    {P P' : ℝ} (hP : P ≤ P') : region H N P ⊆ region H N P' :=
  closure_mono (convexHull_mono (rawRegion_mono H N hP))

theorem region_zero_power
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) : region H N 0 = {0} := by
  simp [region, rawRegion_zero_power H N hN, convexHull_singleton]

theorem region_zero_channel
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) {P : ℝ} (hP : 0 ≤ P) :
    region (0 : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ) N P = {0} := by
  simp [region, rawRegion_zero_channel N hN hP, convexHull_singleton]

theorem isClosed_region
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ) (P : ℝ) :
    IsClosed (region H N P) := isClosed_closure

theorem convex_region
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ) (P : ℝ) :
    Convex ℝ (region H N P) := (convex_convexHull ℝ _).closure

theorem region_nonneg
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    {P : ℝ} {R : Fin K → ℝ} (hR : R ∈ region H N P) (i : Fin K) :
    0 ≤ R i := by
  have hsubset : rawRegion H N P ⊆ {R : Fin K → ℝ | 0 ≤ R i} := fun _ h ↦ h.1 i
  have hconvex : Convex ℝ {R : Fin K → ℝ | 0 ≤ R i} := by
    intro x hx y hy a b ha hb hab
    change 0 ≤ a * x i + b * y i
    exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  exact closure_minimal (convexHull_min hsubset hconvex)
    (isClosed_le continuous_const (continuous_apply i)) hR

end CapacityAtlas.Gaussian.MIMOBroadcast
