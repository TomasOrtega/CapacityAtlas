/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.Basic
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx n : ℕ} {rx : Fin K → ℕ}

/-- A zero average budget forces every codeword coordinate to vanish. -/
theorem encode_eq_zero_of_powerAdmissible_zero (c : Code K tx rx n)
    (hpower : PowerAdmissible 0 c) : c.encode = 0 := by
  have hsum : (∑ m, ∑ s, ∑ a, (c.encode m s a) ^ 2) ≤ 0 := by
    have h := hpower
    rw [PowerAdmissible, mul_zero] at h
    exact nonpos_of_mul_nonpos_right h (inv_pos.mpr (messageCountProduct_pos c))
  have hzero : (∑ m, ∑ s, ∑ a, (c.encode m s a) ^ 2) = 0 :=
    le_antisymm hsum (Finset.sum_nonneg fun _ _ ↦
      Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  ext m s a
  have hm := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)).mp hzero m
      (Finset.mem_univ m)
  have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)).mp hm s (Finset.mem_univ s)
  exact sq_eq_zero_iff.mp ((Finset.sum_eq_zero_iff_of_nonneg
    (fun _ _ ↦ sq_nonneg _)).mp hs a (Finset.mem_univ a))

/-- Identical received signals give exactly one successful tuple per noise realization. -/
theorem error_eq_of_output_eq
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) (x : Fin n → EuclideanSpace ℝ (Fin tx))
    (houtput : ∀ m z i, output H (c.encode m) z i = output H x z i) :
    error H N c = 1 - (∏ i, (c.messages i : ℝ))⁻¹ := by
  classical
  let f := fun z i ↦ (c.decode i).apply (output H x z i)
  have hf (m : (i : Fin K) → Fin (c.messages i)) :
      MeasurableSet (f ⁻¹' {m}) := by
    have heq : f ⁻¹' {m} = {z | ∀ i, f z i = m i} := by
      ext z
      simp [funext_iff]
    rw [heq]
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun i ↦
      ((c.decode i).measurable_fiber (m i)).preimage (measurable_output H x i)
  have hevent (m : (i : Fin K) → Fin (c.messages i)) :
      errorEvent H c m = (f ⁻¹' {m})ᶜ := by
    ext z
    simp only [errorEvent, Set.mem_setOf_eq, houtput, Set.mem_compl_iff,
      Set.mem_preimage, Set.mem_singleton_iff, funext_iff, not_forall]
    rfl
  have hsum : (∑ m, (blockNoise N n).real (f ⁻¹' {m})) = 1 := by
    simpa using sum_measureReal_preimage_singleton (μ := blockNoise N n)
      Finset.univ (fun m _ ↦ hf m)
  change (∏ i, (c.messages i : ℝ))⁻¹ *
    (∑ m, (blockNoise N n).real (errorEvent H c m)) = _
  simp_rw [hevent, measureReal_compl (hf _), probReal_univ]
  rw [Finset.sum_sub_distrib, hsum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, card_messages]
  rw [mul_sub, inv_mul_cancel₀ (ne_of_gt (messageCountProduct_pos c)), mul_one]

theorem error_eq_of_encode_const
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) (x : Fin n → EuclideanSpace ℝ (Fin tx))
    (hencode : ∀ m, c.encode m = x) :
    error H N c = 1 - (∏ i, (c.messages i : ℝ))⁻¹ :=
  error_eq_of_output_eq H N c x (fun m _ _ ↦ by rw [hencode m])

private theorem messages_eq_one_of_counting_error (c : Code K tx rx n)
    (herror : 1 - (∏ i, (c.messages i : ℝ))⁻¹ < (1 / 2 : ℝ)) :
    ∀ i, c.messages i = 1 := by
  intro i
  have hcount : c.messages i ≤ 1 := by
    by_contra h
    have htwo : 2 ≤ c.messages i := by omega
    have hprod : (2 : ℝ) ≤ ∏ j, (c.messages j : ℝ) := by
      have htwo' : (2 : ℝ) ≤ c.messages i := by exact_mod_cast htwo
      refine htwo'.trans ?_
      have hnat : c.messages i ≤ ∏ j, c.messages j :=
        Finset.single_le_prod' (fun j _ ↦ c.messages_pos j) (Finset.mem_univ i)
      exact_mod_cast hnat
    have hinv : (∏ j, (c.messages j : ℝ))⁻¹ ≤ (1 / 2 : ℝ) := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hprod
    linarith
  exact Nat.le_antisymm hcount (c.messages_pos i)

theorem messages_eq_one_of_output_eq_of_error_lt_half
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) (x : Fin n → EuclideanSpace ℝ (Fin tx))
    (houtput : ∀ m z i, output H (c.encode m) z i = output H x z i)
    (herror : error H N c < (1 / 2 : ℝ)) : ∀ i, c.messages i = 1 := by
  apply messages_eq_one_of_counting_error c
  rwa [error_eq_of_output_eq H N c x houtput] at herror

theorem rates_eq_zero_of_output_eq_of_error_lt_half
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) (x : Fin n → EuclideanSpace ℝ (Fin tx))
    (houtput : ∀ m z i, output H (c.encode m) z i = output H x z i)
    (herror : error H N c < (1 / 2 : ℝ)) : rates c = 0 := by
  have hcounts := messages_eq_one_of_output_eq_of_error_lt_half H N c x houtput herror
  ext i
  simp [rates, Operational.messageRate, hcounts i]

private theorem achievable_eq_zero_of_rates_eq_zero
    {ι : Type*} {C : ℕ → Type*} {admissible : ∀ n, C n → Prop}
    {error : ∀ n, C n → ℝ} {rates : ∀ n, C n → ι → ℝ}
    (hzero : ∀ n c, admissible n c → error n c < (1 / 2 : ℝ) → rates n c = 0)
    {R : ι → ℝ} (hR : R ∈ Operational.achievableVectorRegion C admissible error rates) :
    R = 0 := by
  ext i
  apply le_antisymm ?_ (hR.1 i)
  by_contra h
  have hi : 0 < R i := lt_of_not_ge h
  let ε : ℝ := min (1 / 4) (R i / 2)
  have hε : 0 < ε := lt_min (by norm_num) (half_pos hi)
  obtain ⟨N, _, hcodes⟩ := hR.2 ε hε
  obtain ⟨c, hc, he, hrates⟩ := hcodes N le_rfl
  have her : error N c < (1 / 2 : ℝ) :=
    lt_of_le_of_lt (he.trans (min_le_left _ _)) (by norm_num)
  have hz := congrFun (hzero N c hc her) i
  have hr := hrates i
  change rates N c i = 0 at hz
  rw [hz] at hr
  have hεi : ε ≤ R i / 2 := min_le_right _ _
  linarith

theorem capacityRegion_zero_power_subset
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ) :
    capacityRegion H N 0 ⊆ {0} := by
  apply closure_minimal _ isClosed_singleton
  intro R hR
  apply Set.mem_singleton_iff.mpr
  apply achievable_eq_zero_of_rates_eq_zero (R := R) _ hR
  intro n c hc he
  have hencode := encode_eq_zero_of_powerAdmissible_zero c hc
  apply rates_eq_zero_of_output_eq_of_error_lt_half H N c 0 _ he
  intro m z i
  rw [hencode]
  rfl

theorem error_zero_channel
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) :
    error 0 N c = 1 - (∏ i, (c.messages i : ℝ))⁻¹ := by
  apply error_eq_of_output_eq 0 N c 0
  intro m z i
  ext s a
  simp [output]

theorem capacityRegion_zero_channel_subset
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ) (P : ℝ) :
    capacityRegion (0 : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ) N P ⊆ {0} := by
  apply closure_minimal _ isClosed_singleton
  intro R hR
  apply Set.mem_singleton_iff.mpr
  apply achievable_eq_zero_of_rates_eq_zero (R := R) _ hR
  intro n c _ he
  apply rates_eq_zero_of_output_eq_of_error_lt_half 0 N c 0 _ he
  intro m z i
  ext s a
  simp [output]

theorem capacityRegion_zero_power
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ) :
    capacityRegion H N 0 = {0} := by
  apply Set.Subset.antisymm (capacityRegion_zero_power_subset H N)
  intro R hR
  obtain rfl := Set.mem_singleton_iff.mp hR
  exact zero_mem_capacityRegion H N le_rfl

theorem capacityRegion_zero_channel
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    {P : ℝ} (hP : 0 ≤ P) :
    capacityRegion (0 : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ) N P = {0} := by
  apply Set.Subset.antisymm (capacityRegion_zero_channel_subset N P)
  intro R hR
  obtain rfl := Set.mem_singleton_iff.mp hR
  exact zero_mem_capacityRegion 0 N hP

end CapacityAtlas.Gaussian.MIMOBroadcast
