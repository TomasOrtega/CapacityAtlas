/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.Optimization
import CapacityAtlasForMathlib.LinearAlgebra.LogDet
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open scoped BigOperators

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx : ℕ} {rx : Fin K → ℕ}

lemma prefixCovariance_add_smul (Q D : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) (t : ℝ) :
    prefixCovariance (Q + t • D) π k = prefixCovariance Q π k + t • prefixCovariance D π k := by
  simp [prefixCovariance, Finset.sum_add_distrib, Finset.smul_sum]

lemma receivedCovariance_add_smul {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q D : Matrix (Fin tx) (Fin tx) ℝ) (t : ℝ) :
    receivedCovariance H N (Q + t • D) =
      receivedCovariance H N Q + t • (H * D * H.transpose) := by
  simp [receivedCovariance, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, add_assoc]

noncomputable def dpcRateVariation
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q D : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (π : Equiv.Perm (Fin K)) (k : Fin K) : ℝ :=
  (Matrix.trace ((receivedCovariance (H (π k)) (N (π k))
      (prefixCovariance Q π k + Q (π k)))⁻¹ *
        (H (π k) * (prefixCovariance D π k + D (π k)) * (H (π k)).transpose)) -
    Matrix.trace ((receivedCovariance (H (π k)) (N (π k)) (prefixCovariance Q π k))⁻¹ *
      (H (π k) * prefixCovariance D π k * (H (π k)).transpose))) / (2 * Real.log 2)

theorem hasDerivAt_dpcRate_allocation
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) (Q D : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (hQ : ∀ i, (Q i).PosSemidef) (π : Equiv.Perm (Fin K)) (k : Fin K) :
    HasDerivAt (fun t : ℝ ↦ dpcRate H N (Q + t • D) π k) (dpcRateVariation H N Q D π k) 0 := by
  have hnum (t : ℝ) : prefixCovariance (Q + t • D) π k + (Q + t • D) (π k) =
      (prefixCovariance Q π k + Q (π k)) + t • (prefixCovariance D π k + D (π k)) := by
    rw [prefixCovariance_add_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_add]
    abel
  unfold dpcRate
  simp_rw [hnum, prefixCovariance_add_smul, receivedCovariance_add_smul, Real.logb]
  have h := ((Matrix.hasDerivAt_log_det_div_add_smul
    (receivedCovariance (H (π k)) (N (π k)) (prefixCovariance Q π k + Q (π k)))
    (H (π k) * (prefixCovariance D π k + D (π k)) * (H (π k)).transpose)
    (receivedCovariance (H (π k)) (N (π k)) (prefixCovariance Q π k))
    (H (π k) * prefixCovariance D π k * (H (π k)).transpose)
    (dpcRate_numerator_pos H N Q hN hQ π k).ne'
    (dpcRate_denominator_pos H N Q hN hQ π k).ne').div_const (Real.log 2)).const_mul (1 / 2)
  apply h.congr_deriv
  unfold dpcRateVariation
  ring

theorem hasDerivAt_weightedDpcRate_allocation (w : Fin K → ℝ)
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) (Q D : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (hQ : ∀ i, (Q i).PosSemidef) (π : Equiv.Perm (Fin K)) :
    HasDerivAt (fun t : ℝ ↦ weightedDpcRate w H N (Q + t • D) π)
      (∑ k, w (π k) * dpcRateVariation H N Q D π k) 0 := by
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun k _ ↦
    (hasDerivAt_dpcRate_allocation H N hN Q D hQ π k).const_mul (w (π k)))

theorem convex_allocationAdmissible (P : ℝ) :
    Convex ℝ {Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ | AllocationAdmissible P Q} := by
  intro Q hQ D hD a b ha hb hab
  refine ⟨fun i ↦ ((hQ.1 i).smul ha).add ((hD.1 i).smul hb), ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  exact (add_le_add (mul_le_mul_of_nonneg_left hQ.2 ha)
    (mul_le_mul_of_nonneg_left hD.2 hb)).trans_eq (by rw [← add_mul, hab, one_mul])

/-- Every feasible direction has nonpositive weighted-rate derivative at a maximizing allocation. -/
theorem weightedDpcRate_variation_nonpos (w : Fin K → ℝ)
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) {P : ℝ}
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (hQ : AllocationAdmissible P Q)
    (π : Equiv.Perm (Fin K))
    (hmax : ∀ Q', AllocationAdmissible P Q' →
      weightedDpcRate w H N Q' π ≤ weightedDpcRate w H N Q π)
    (Q' : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (hQ' : AllocationAdmissible P Q') :
    ∑ k, w (π k) * dpcRateVariation H N Q (Q' - Q) π k ≤ 0 := by
  have hfeasible (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      AllocationAdmissible P (Q + t • (Q' - Q)) := by
    rw [show Q + t • (Q' - Q) = (1 - t) • Q + t • Q' by module]
    exact convex_allocationAdmissible P hQ hQ' (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hm : IsMaxOn (fun t : ℝ ↦ weightedDpcRate w H N (Q + t • (Q' - Q)) π)
      (Set.Icc (0 : ℝ) 1) 0 := by
    intro t ht
    simpa only [Set.mem_setOf_eq, zero_smul, add_zero] using hmax _ (hfeasible t ht)
  have htangent : (1 : ℝ) ∈ posTangentConeAt (Set.Icc (0 : ℝ) 1) 0 := by
    simpa only [sub_zero] using sub_mem_posTangentConeAt_of_segment_subset
      (show segment ℝ (0 : ℝ) 1 ⊆ Set.Icc 0 1 by rw [segment_eq_Icc zero_le_one])
  have hd := hasDerivAt_weightedDpcRate_allocation w H N hN Q (Q' - Q) hQ.1 π
  simpa using hm.localize.hasFDerivWithinAt_nonpos hd.hasFDerivAt.hasFDerivWithinAt htangent

theorem exists_weightedDpcRate_max_firstOrder (w : Fin K → ℝ)
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) {P : ℝ} (hP : 0 ≤ P) :
    ∃ Q, AllocationAdmissible P Q ∧ ∃ π,
      (∀ Q', AllocationAdmissible P Q' → ∀ π',
        weightedDpcRate w H N Q' π' ≤ weightedDpcRate w H N Q π) ∧
      ∀ Q', AllocationAdmissible P Q' →
        ∑ k, w (π k) * dpcRateVariation H N Q (Q' - Q) π k ≤ 0 := by
  obtain ⟨Q, hQ, π, hmax⟩ := exists_weightedDpcRate_max w H N hN hP
  exact ⟨Q, hQ, π, hmax,
    weightedDpcRate_variation_nonpos w H N hN Q hQ π (fun Q' hQ' ↦ hmax Q' hQ' π)⟩

end CapacityAtlas.Gaussian.MIMOBroadcast
