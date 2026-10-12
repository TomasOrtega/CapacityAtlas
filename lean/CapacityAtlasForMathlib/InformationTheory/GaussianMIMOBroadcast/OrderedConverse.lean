/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.EnhancedEntropy
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.OperationalEnhancement
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.AlignmentLimit

open Matrix MeasureTheory ProbabilityTheory Filter
open scoped ENNReal MatrixOrder Topology

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {m tx : ℕ} {rx : Fin (m + 1) → ℕ}

theorem alignedLogObjective_half_eq_log_weightedDpcRate (w : Fin (m + 1) → ℝ)
    (E Q : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ)
    (hE : ∀ k, (E k).PosDef) (hQ : ∀ k, (Q k).PosSemidef) :
    alignedLogObjective w E Q / 2 = Real.log 2 *
      weightedDpcRate w (fun _ ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) E Q (Equiv.refl _) := by
  rw [weightedDpcRate_eq_alignedLogObjective w E Q hE hQ]
  unfold alignedLogObjective
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  field_simp

theorem weighted_log_messages_eq {n : ℕ} (c : Code (m + 1) tx rx n) (hn : 0 < n)
    (w : Fin (m + 1) → ℝ) :
    (∑ i, w i * Real.log (c.messages i)) = n * Real.log 2 * ∑ i, w i * rates c i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold rates Operational.messageRate Real.logb
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp

theorem exists_alignmentNoise_code_bound
    (H : (i : Fin (m + 1)) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin (m + 1)) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) (htx : 0 < tx)
    (w : Fin (m + 1) → ℝ) (hw : ∀ i, 0 < w i) (hm : Monotone w)
    {P δ : ℝ} (hP : 0 < P) (hδ : 0 < δ) :
    ∃ Q, AllocationAdmissible P Q ∧ ∀ n, 0 < n → ∀ c : Code (m + 1) tx rx n,
      PowerAdmissible P c →
      (1 - error H N c) * (∑ i, w i * rates c i) ≤
        weightedDpcRate w (fun _ ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ))
          (fun i ↦ alignmentNoise (H i) (N i) δ) Q (Equiv.refl _) + (∑ i, w i) / n := by
  obtain ⟨Q, hQ, E, hE, hle, _, hrates, hprop, lam, hlam, hstat, hcomp, _⟩ :=
    exists_aligned_operational_enhancement (fun i ↦ alignmentNoise (H i) (N i) δ)
      (fun i ↦ alignmentNoise_posDef (H i) (N i) (hN i) hδ) w hw hm hP
  refine ⟨Q, hQ, fun n hn c hc ↦ ?_⟩
  have hf := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
    mul_le_mul_of_nonneg_left (fano_receiver_enhanced_alignment H N c i (hN i) hδ
      (E i) (hE i) (hle i)) (hw i).le)
  simp only [mul_add, Finset.sum_add_distrib] at hf
  have he := weighted_codePrefixEntropy_le c htx hn w E Q hw hm hE hc hlam hQ hprop hstat hcomp
  rw [alignedLogObjective_half_eq_log_weightedDpcRate w E Q hE hQ.1] at he
  have hr : weightedDpcRate w (fun _ ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) E Q (Equiv.refl _) =
      weightedDpcRate w (fun _ ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ))
        (fun i ↦ alignmentNoise (H i) (N i) δ) Q (Equiv.refl _) := by
    unfold weightedDpcRate
    simp_rw [hrates]
  rw [hr] at he
  have hsum : (∑ i, w i * (error H N c * Real.log (c.messages i))) =
      error H N c * ∑ i, w i * Real.log (c.messages i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum, ← Finset.sum_mul, weighted_log_messages_eq c hn w] at hf
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (mul_le_mul_iff_right₀ (mul_pos hn' hl)).mp
  have hdiv : (n * Real.log 2) * ((∑ i, w i) / (n : ℝ)) = (∑ i, w i) * Real.log 2 := by
    field_simp
  rw [mul_add, hdiv]
  nlinarith

variable {K n : ℕ} {rx : Fin K → ℕ}

theorem weighted_rates_nonneg (c : Code K tx rx n) (w : Fin K → ℝ) (hw : ∀ i, 0 ≤ w i) :
    0 ≤ ∑ i, w i * rates c i := by
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (hw i)
  unfold rates Operational.messageRate
  apply div_nonneg _ (Nat.cast_nonneg n)
  exact Real.logb_nonneg (by norm_num) (by exact_mod_cast c.messages_pos i)

theorem capacity_weighted_le_of_code_bounds
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (w : Fin K → ℝ) (hw : ∀ i, 0 ≤ w i) {P b : ℝ}
    (hbound : ∀ n, 0 < n → ∀ c : Code K tx rx n, PowerAdmissible P c →
      (1 - error H N c) * (∑ i, w i * rates c i) ≤ b + (∑ i, w i) / n)
    {R : Fin K → ℝ} (hR : R ∈ capacityRegion H N P) : ∑ i, w i * R i ≤ b := by
  rw [capacityRegion_eq_achievableVectorRegion] at hR
  have heps (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
      (1 - ε) * ((∑ i, w i * R i) - ε * ∑ i, w i) ≤ b := by
    obtain ⟨L, hL, hcodes⟩ := hR.2 ε hε
    have hlim : Tendsto (fun n : ℕ ↦ b + (∑ i, w i) / (n : ℝ)) atTop (𝓝 b) := by
      simpa only [div_eq_mul_inv, mul_zero, add_zero] using tendsto_const_nhds.add
        (tendsto_const_nhds.mul (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)))
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop L] with n hn
    obtain ⟨c, hc, herr, hrates⟩ := hcodes n hn
    have hrate := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
      mul_le_mul_of_nonneg_left (hrates i) (hw i))
    have he := mul_le_mul_of_nonneg_right (sub_le_sub_left herr 1) (weighted_rates_nonneg c w hw)
    have hscaled := mul_le_mul_of_nonneg_left hrate (sub_pos.mpr hε1).le
    have hb := hbound n (hL.trans_le hn) c hc
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at hscaled
    nlinarith
  have hlim : Tendsto (fun ε : ℝ ↦ (1 - ε) * ((∑ i, w i * R i) - ε * ∑ i, w i))
      (𝓝[>] 0) (𝓝 (∑ i, w i * R i)) := by
    have h : Continuous (fun ε : ℝ ↦ (1 - ε) * ((∑ i, w i * R i) - ε * ∑ i, w i)) := by fun_prop
    simpa using h.continuousAt.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin, eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num) |>.filter_mono inf_le_left]
    with ε hε hε1
  exact heps ε hε hε1

variable {rx : Fin (m + 1) → ℕ}

theorem exists_capacity_weighted_bound_ordered
    (H : (i : Fin (m + 1)) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin (m + 1)) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) (htx : 0 < tx)
    (w : Fin (m + 1) → ℝ) (hw : ∀ i, 0 < w i) (hm : Monotone w)
    {P : ℝ} (hP : 0 < P) {R : Fin (m + 1) → ℝ} (hR : R ∈ capacityRegion H N P) :
    ∃ Q, AllocationAdmissible P Q ∧ (∑ i, w i * R i) ≤ weightedDpcRate w H N Q (Equiv.refl _) := by
  obtain ⟨Q, hQ, hmax⟩ := exists_weightedDpcRate_max_for_order w H N hN (Equiv.refl _) hP.le
  refine ⟨Q, hQ, le_of_forall_alignmentNoise_support_bound w H N hN (Equiv.refl _) P
    (weightedDpcRate w H N Q (Equiv.refl _)) (∑ i, w i * R i) hmax ?_⟩
  intro δ hδ
  obtain ⟨Y, hY, hb⟩ := exists_alignmentNoise_code_bound H N hN htx w hw hm hP hδ
  exact ⟨Y, hY, capacity_weighted_le_of_code_bounds H N w (fun i ↦ (hw i).le) hb hR⟩

end CapacityAtlas.Gaussian.MIMOBroadcast
