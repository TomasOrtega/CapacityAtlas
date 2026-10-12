/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.KKT

open Matrix
open scoped BigOperators

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx : ℕ} {rx : Fin K → ℕ}

noncomputable def receivedPrecision {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (S : Matrix (Fin tx) (Fin tx) ℝ) :
    Matrix (Fin tx) (Fin tx) ℝ := H.transpose * (receivedCovariance H N S)⁻¹ * H

lemma receivedPrecision_isHermitian {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (S : Matrix (Fin tx) (Fin tx) ℝ)
    (hN : N.PosDef) (hS : S.PosSemidef) : (receivedPrecision H N S).IsHermitian := by
  simpa [receivedPrecision] using isHermitian_conjTranspose_mul_mul H
    (receivedCovariance_posDef H N S hN hS).isHermitian.inv

lemma trace_receivedPrecision_mul {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (S D : Matrix (Fin tx) (Fin tx) ℝ) :
    trace ((receivedCovariance H N S)⁻¹ * (H * D * H.transpose)) =
      trace (receivedPrecision H N S * D) := by
  unfold receivedPrecision
  rw [← Matrix.mul_assoc, trace_mul_cycle]
  simp only [Matrix.mul_assoc]

lemma sum_trace_prefixCovariance (C D : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) :
    (∑ k, trace (C k * prefixCovariance D π k)) =
      ∑ j, trace ((∑ k ∈ Finset.univ.filter (fun k : Fin K ↦ j < k), C k) * D (π j)) := by
  simp only [prefixCovariance, Matrix.mul_sum, Matrix.sum_mul, trace_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [mul_ite, ite_mul, Matrix.mul_zero, Matrix.zero_mul, apply_ite trace, trace_zero]

noncomputable def cumulativeGradient (A B : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (i : Fin K) : Matrix (Fin tx) (Fin tx) ℝ :=
  A (π.symm i) + ∑ k ∈ Finset.univ.filter (fun k : Fin K ↦ π.symm i < k), (A k - B k)

lemma traceObjective_cumulativeGradient (A B D : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) :
    (∑ k, (trace (A k * (prefixCovariance D π k + D (π k))) -
      trace (B k * prefixCovariance D π k))) = traceObjective (cumulativeGradient A B π) D := by
  unfold traceObjective
  rw [← Equiv.sum_comp π (fun i ↦ trace (cumulativeGradient A B π i * D i))]
  simp only [cumulativeGradient, Equiv.symm_apply_apply, Matrix.add_mul, trace_add,
    Finset.sum_add_distrib]
  rw [← sum_trace_prefixCovariance]
  simp only [Matrix.mul_add, trace_add, Matrix.sub_mul, trace_sub,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

noncomputable def dpcGradient (w : Fin K → ℝ)
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (π : Equiv.Perm (Fin K)) :
    Fin K → Matrix (Fin tx) (Fin tx) ℝ :=
  cumulativeGradient
    (fun k ↦ (w (π k) / (2 * Real.log 2)) • receivedPrecision (H (π k)) (N (π k))
      (prefixCovariance Q π k + Q (π k)))
    (fun k ↦ (w (π k) / (2 * Real.log 2)) • receivedPrecision (H (π k)) (N (π k))
      (prefixCovariance Q π k)) π

theorem weightedDpcRate_variation_eq_traceObjective (w : Fin K → ℝ)
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q D : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (π : Equiv.Perm (Fin K)) :
    (∑ k, w (π k) * dpcRateVariation H N Q D π k) =
      traceObjective (dpcGradient w H N Q π) D := by
  unfold dpcGradient
  rw [← traceObjective_cumulativeGradient]
  apply Finset.sum_congr rfl
  intro k _
  simp only [dpcRateVariation, trace_receivedPrecision_mul, Matrix.smul_mul,
    trace_smul, smul_eq_mul]
  ring

lemma cumulativeGradient_isHermitian (A B : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (hA : ∀ k, (A k).IsHermitian) (hB : ∀ k, (B k).IsHermitian)
    (π : Equiv.Perm (Fin K)) (i : Fin K) : (cumulativeGradient A B π i).IsHermitian := by
  apply (hA _).add
  simp only [IsHermitian, conjTranspose_sum]
  exact Finset.sum_congr rfl (fun k _ ↦ (hA k).sub (hB k))

theorem dpcGradient_isHermitian (w : Fin K → ℝ)
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (hQ : ∀ i, (Q i).PosSemidef) (π : Equiv.Perm (Fin K)) (i : Fin K) :
    (dpcGradient w H N Q π i).IsHermitian := by
  apply cumulativeGradient_isHermitian
  · intro k
    exact (receivedPrecision_isHermitian _ _ _ (hN (π k))
      ((prefixCovariance_posSemidef Q hQ π k).add (hQ (π k)))).smul (IsSelfAdjoint.all _)
  · intro k
    exact (receivedPrecision_isHermitian _ _ _ (hN (π k))
      (prefixCovariance_posSemidef Q hQ π k)).smul (IsSelfAdjoint.all _)

lemma traceObjective_sub (G Q D : Fin K → Matrix (Fin tx) (Fin tx) ℝ) :
    traceObjective G (Q - D) = traceObjective G Q - traceObjective G D := by
  simp only [traceObjective, Pi.sub_apply, Matrix.mul_sub, trace_sub, Finset.sum_sub_distrib]

/-- The concrete DPC optimizer has matrix multipliers with no added regularity hypotheses. -/
theorem exists_weightedDpcRate_max_multipliers (w : Fin K → ℝ)
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) {P : ℝ} (hP : 0 < P) :
    ∃ Q, AllocationAdmissible P Q ∧ ∃ π,
      (∀ Q', AllocationAdmissible P Q' → ∀ π',
        weightedDpcRate w H N Q' π' ≤ weightedDpcRate w H N Q π) ∧
      ∃ lam : ℝ, 0 ≤ lam ∧ ∃ M : Fin K → Matrix (Fin tx) (Fin tx) ℝ,
        (∀ i, (M i).PosSemidef) ∧ (∀ i, dpcGradient w H N Q π i + M i = lam • 1) ∧
        (∀ i, M i * Q i = 0) ∧ lam * (P - ∑ i, trace (Q i)) = 0 := by
  obtain ⟨Q, hQ, π, hmax, hvar⟩ := exists_weightedDpcRate_max_firstOrder w H N hN hP.le
  refine ⟨Q, hQ, π, hmax, exists_traceBudget_multipliers hP _ Q hQ
    (dpcGradient_isHermitian w H N hN Q hQ.1 π) ?_⟩
  intro Y hY
  have h := hvar Y hY
  rw [weightedDpcRate_variation_eq_traceObjective, traceObjective_sub] at h
  exact sub_nonpos.mp h

end CapacityAtlas.Gaussian.MIMOBroadcast
