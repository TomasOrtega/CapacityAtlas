/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.Alignment
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.Optimization
import CapacityAtlasForMathlib.LinearAlgebra.NoiseEnhancement

open Matrix Filter Topology

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {ι ο : Type*} [Fintype ι] [Fintype ο] [DecidableEq ι] [DecidableEq ο]

noncomputable def regularizedDet (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (δ : ℝ) (S : Matrix ι ι ℝ) : ℝ :=
  (1 + S * (δ • 1 + H.transpose * N⁻¹ * H)).det

theorem regularizedDet_eq_ratio (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (hN : N.PosDef) {δ : ℝ} (hδ : 0 < δ) (S : Matrix ι ι ℝ) :
    regularizedDet H N δ S = (alignmentNoise H N δ + S).det / (alignmentNoise H N δ).det := by
  rw [add_comm (alignmentNoise H N δ) S,
    Matrix.det_add_div_det_eq_det_one_add (alignmentNoise_posDef H N hN hδ),
    alignmentNoise_inv H N hN hδ]
  rfl

theorem regularizedDet_zero (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (hN : N.PosDef) (S : Matrix ι ι ℝ) :
    regularizedDet H N 0 S = (N + H * S * H.transpose).det / N.det := by
  rw [add_comm N, Matrix.det_add_div_det_eq_det_one_add hN]
  simp only [regularizedDet, zero_smul, zero_add]
  calc
    _ = (1 + (S * H.transpose * N⁻¹) * H).det := by simp only [Matrix.mul_assoc]
    _ = (1 + H * (S * H.transpose * N⁻¹)).det := Matrix.det_one_add_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

theorem regularizedDet_pos (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (hN : N.PosDef) {δ : ℝ} (hδ : 0 ≤ δ) (S : Matrix ι ι ℝ) (hS : S.PosSemidef) :
    0 < regularizedDet H N δ S := by
  obtain rfl | hδ := hδ.eq_or_lt
  · rw [regularizedDet_zero H N hN S]
    exact div_pos (DirtyPaper.outputCovariance_posDef H S N hS hN).det_pos hN.det_pos
  · rw [regularizedDet_eq_ratio H N hN hδ]
    exact div_pos ((alignmentNoise_posDef H N hN hδ).add_posSemidef hS).det_pos
      (alignmentNoise_posDef H N hN hδ).det_pos

theorem continuous_regularizedDet (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ) :
    Continuous (fun p : ℝ × Matrix ι ι ℝ ↦ regularizedDet H N p.1 p.2) := by
  unfold regularizedDet
  fun_prop

variable {K tx : ℕ} {rx : Fin K → ℕ}

noncomputable def regularizedDpcRate
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (δ : ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) : ℝ :=
  (1 / 2 : ℝ) * Real.logb 2
    (regularizedDet (H (π k)) (N (π k)) δ (prefixCovariance Q π k + Q (π k)) /
      regularizedDet (H (π k)) (N (π k)) δ (prefixCovariance Q π k))

theorem regularizedDpcRate_eq_aligned
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) {δ : ℝ} (hδ : 0 < δ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (π : Equiv.Perm (Fin K)) (k : Fin K) :
    regularizedDpcRate H N δ Q π k =
      dpcRate (fun _ : Fin K ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) (fun i ↦ alignmentNoise (H i) (N i) δ) Q π k := by
  unfold regularizedDpcRate dpcRate
  simp only [regularizedDet_eq_ratio _ _ (hN _) hδ,
    div_div_div_cancel_right₀ (alignmentNoise_posDef _ _ (hN _) hδ).det_pos.ne',
    receivedCovariance, transpose_one, one_mul, mul_one]

theorem regularizedDpcRate_zero
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (π : Equiv.Perm (Fin K)) (k : Fin K) :
    regularizedDpcRate H N 0 Q π k = dpcRate H N Q π k := by
  unfold regularizedDpcRate dpcRate
  simp only [regularizedDet_zero _ _ (hN _),
    div_div_div_cancel_right₀ (hN _).det_pos.ne', receivedCovariance]

theorem continuousAt_regularizedDpcRate
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) (π : Equiv.Perm (Fin K)) (k : Fin K)
    {δ : ℝ} (hδ : 0 ≤ δ) {Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ}
    (hQ : ∀ i, (Q i).PosSemidef) :
    ContinuousAt (fun p : ℝ × (Fin K → Matrix (Fin tx) (Fin tx) ℝ) ↦
      regularizedDpcRate H N p.1 p.2 π k) (δ, Q) := by
  unfold regularizedDpcRate
  apply continuousAt_const.mul
  apply ContinuousAt.logb
  · apply ContinuousAt.div
    · unfold regularizedDet prefixCovariance
      fun_prop
    · unfold regularizedDet prefixCovariance
      fun_prop
    · exact (regularizedDet_pos _ _ (hN _) hδ _ (prefixCovariance_posSemidef Q hQ π k)).ne'
  · exact (div_pos
      (regularizedDet_pos _ _ (hN _) hδ _ ((prefixCovariance_posSemidef Q hQ π k).add (hQ _)))
      (regularizedDet_pos _ _ (hN _) hδ _ (prefixCovariance_posSemidef Q hQ π k))).ne'

theorem dpcRate_alignmentNoise_tendsto
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (hQ : ∀ i, (Q i).PosSemidef) (π : Equiv.Perm (Fin K)) (k : Fin K) :
    Tendsto (fun δ ↦ dpcRate (fun _ : Fin K ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) (fun i ↦ alignmentNoise (H i) (N i) δ) Q π k)
      (𝓝[>] 0) (𝓝 (dpcRate H N Q π k)) := by
  have h := (continuousAt_regularizedDpcRate H N hN π k (δ := 0) le_rfl hQ).tendsto.comp
    (tendsto_id.prodMk_nhds tendsto_const_nhds)
  rw [regularizedDpcRate_zero H N hN Q π k] at h
  apply (h.mono_left inf_le_left).congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact regularizedDpcRate_eq_aligned H N hN hδ Q π k

theorem eventually_weightedDpcRate_alignmentNoise_lt
    (w : Fin K → ℝ)
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) (π : Equiv.Perm (Fin K)) (P b : ℝ)
    (hbound : ∀ Q, AllocationAdmissible P Q → weightedDpcRate w H N Q π ≤ b)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ δ in 𝓝[>] 0, ∀ Q, AllocationAdmissible P Q →
      weightedDpcRate w (fun _ : Fin K ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) (fun i ↦ alignmentNoise (H i) (N i) δ) Q π < b + ε := by
  have h : ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ Q, AllocationAdmissible P Q →
      (∑ k, w (π k) * regularizedDpcRate H N δ Q π k) < b + ε := by
    apply (isCompact_allocationAdmissible P).eventually_forall_of_forall_eventually
    intro Q hQ
    have hc : ContinuousAt (fun p : ℝ × (Fin K → Matrix (Fin tx) (Fin tx) ℝ) ↦
        ∑ k, w (π k) * regularizedDpcRate H N p.1 p.2 π k) (0, Q) := by
      apply tendsto_finsetSum
      intro k _
      exact continuousAt_const.mul (continuousAt_regularizedDpcRate H N hN π k le_rfl hQ.1)
    apply hc.tendsto.eventually_lt_const
    simp only [regularizedDpcRate_zero H N hN]
    exact (hbound Q hQ).trans_lt (lt_add_of_pos_right b hε)
  filter_upwards [h.filter_mono inf_le_left, self_mem_nhdsWithin] with δ hδ hδpos
  intro Q hQ
  simpa only [weightedDpcRate, regularizedDpcRate_eq_aligned H N hN hδpos] using hδ Q hQ

theorem le_of_forall_alignmentNoise_support_bound
    (w : Fin K → ℝ)
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) (π : Equiv.Perm (Fin K)) (P b r : ℝ)
    (hbound : ∀ Q, AllocationAdmissible P Q → weightedDpcRate w H N Q π ≤ b)
    (hr : ∀ δ, 0 < δ → ∃ Q, AllocationAdmissible P Q ∧ r ≤
      weightedDpcRate w (fun _ : Fin K ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) (fun i ↦ alignmentNoise (H i) (N i) δ) Q π) : r ≤ b := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have he := eventually_weightedDpcRate_alignmentNoise_lt w H N hN π P b hbound hε
  obtain ⟨δ, hδ, hδpos⟩ := (he.and self_mem_nhdsWithin).exists
  obtain ⟨Q, hQ, hrQ⟩ := hr δ hδpos
  exact (hrQ.trans_lt (hδ Q hQ)).le

end CapacityAtlas.Gaussian.MIMOBroadcast
