/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.CodeConverse
import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.BasicFacts
import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.ConverseAsymptotics

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace CapacityAtlas.Gaussian.Interference

theorem rates_nonneg {K n : ℕ} (c : Code K n) (i : Fin K) : 0 ≤ rates c i := by
  unfold rates Operational.messageRate
  apply div_nonneg _ (Nat.cast_nonneg n)
  exact Real.logb_nonneg (by norm_num) (by exact_mod_cast c.messages_pos i)

theorem code_pair_rates_bound (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {L U P : ℝ} (hL : 0 < L) (hU : 0 ≤ U) (hP : 0 ≤ P)
    (hμ : ∀ᵐ z ∂μ, L ≤ ‖z‖ ∧ ‖z‖ ≤ U)
    {K n : ℕ} (hn : 0 < n) (c : Code K n) (hc : PowerAdmissible μ P c)
    (i j : Fin K) (hij : i ≠ j) :
    (1 - error μ c) * (rates c i + rates c j) ≤
      Real.logb 2 (1 + U ^ 2 * P / converseNoise L U) + 2 / n := by
  have hf := code_pair_converse μ hL hU hP hμ c hc i j hij
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd := div_le_div_of_nonneg_right hf (mul_pos hnR hlog).le
  calc
    _ = ((1 - error μ c) * (Real.log (c.messages i) + Real.log (c.messages j))) /
        ((n : ℝ) * Real.log 2) := by unfold rates Operational.messageRate Real.logb; ring
    _ ≤ _ := hd
    _ = _ := by
      unfold Real.logb
      field_simp

theorem capacityRegion_pair_bound (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {L U P : ℝ} (hL : 0 < L) (hU : 0 ≤ U) (hP : 0 ≤ P)
    (hμ : ∀ᵐ z ∂μ, L ≤ ‖z‖ ∧ ‖z‖ ≤ U)
    {K : ℕ} {R : Fin K → ℝ} (hR : R ∈ capacityRegion μ K P)
    (i j : Fin K) (hij : i ≠ j) :
    R i + R j ≤ Real.logb 2 (1 + U ^ 2 * P / converseNoise L U) := by
  let B := Real.logb 2 (1 + U ^ 2 * P / converseNoise L U)
  have heps (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
      (1 - ε) * (R i + R j - 2 * ε) ≤ B := by
    obtain ⟨N, hN, hcodes⟩ := hR.2 ε hε
    have hlim : Tendsto (fun n : ℕ ↦ B + 2 / (n : ℝ)) atTop (𝓝 B) := by
      simpa only [div_eq_mul_inv, mul_zero, add_zero] using tendsto_const_nhds.add
        (tendsto_const_nhds.mul (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)))
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop N] with n hn
    obtain ⟨c, hc, herr, hrates⟩ := hcodes n hn
    have hrate : R i + R j - 2 * ε ≤ rates c i + rates c j := by
      linarith [hrates i, hrates j]
    have hscaled := mul_le_mul_of_nonneg_left hrate (sub_pos.mpr hε1).le
    have herrscaled := mul_le_mul_of_nonneg_right (sub_le_sub_left herr 1)
      (add_nonneg (rates_nonneg c i) (rates_nonneg c j))
    have hb := code_pair_rates_bound μ hL hU hP hμ (hN.trans_le hn) c hc i j hij
    dsimp only [B]
    nlinarith
  have hlim : Tendsto (fun ε : ℝ ↦ (1 - ε) * (R i + R j - 2 * ε))
      (𝓝[>] 0) (𝓝 (R i + R j)) := by
    have h : Continuous (fun ε : ℝ ↦ (1 - ε) * (R i + R j - 2 * ε)) := by fun_prop
    simpa using h.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num) |>.filter_mono inf_le_left]
    with ε hε hε1
  exact heps ε hε hε1

theorem capacityRegion_sum_bound (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {L U P : ℝ} (hL : 0 < L) (hU : 0 ≤ U) (hP : 0 ≤ P)
    (hμ : ∀ᵐ z ∂μ, L ≤ ‖z‖ ∧ ‖z‖ ≤ U)
    {K : ℕ} (hK : 2 ≤ K) {R : Fin K → ℝ} (hR : R ∈ capacityRegion μ K P) :
    (∑ i, R i) ≤ (K : ℝ) / 2 * Real.logb 2 (1 + U ^ 2 * P / converseNoise L U) :=
  sum_le_of_pair_bounds hK R _ (fun i j hij ↦ capacityRegion_pair_bound μ hL hU hP hμ hR i j hij)

theorem sumCapacity_converse (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {L U P : ℝ} (hL : 0 < L) (hU : 0 ≤ U) (hP : 0 ≤ P)
    (hμ : ∀ᵐ z ∂μ, L ≤ ‖z‖ ∧ ‖z‖ ≤ U) {K : ℕ} (hK : 2 ≤ K) :
    sumCapacity μ K P ≤
      (K : ℝ) / 2 * Real.logb 2 (1 + U ^ 2 * P / converseNoise L U) :=
  sumCapacity_le hP (fun _ hR ↦ capacityRegion_sum_bound μ hL hU hP hμ hK hR)

theorem sumRates_bddAbove (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {L U P : ℝ} (hL : 0 < L) (hU : 0 ≤ U) (hP : 0 ≤ P)
    (hμ : ∀ᵐ z ∂μ, L ≤ ‖z‖ ∧ ‖z‖ ≤ U) {K : ℕ} (hK : 2 ≤ K) :
    BddAbove {s | ∃ R ∈ capacityRegion μ K P, s = ∑ i, R i} :=
  sumRates_bddAbove_of_bound (fun _ hR ↦ capacityRegion_sum_bound μ hL hU hP hμ hK hR)

theorem sumRates_bddAbove_all (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {L U : ℝ} (hL : 0 < L) (hU : 0 ≤ U)
    (hμ : ∀ᵐ z ∂μ, L ≤ ‖z‖ ∧ ‖z‖ ≤ U) {K : ℕ} (hK : 2 ≤ K) (P : ℝ) :
    BddAbove {s | ∃ R ∈ capacityRegion μ K P, s = ∑ i, R i} := by
  obtain ⟨B, hB⟩ := sumRates_bddAbove μ hL hU (le_max_right P 0) hμ hK
  refine ⟨B, ?_⟩
  rintro s ⟨R, hR, rfl⟩
  exact hB ⟨R, capacityRegion_mono μ K (le_max_left P 0) hR, rfl⟩

theorem sumCapacity_monotone (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {L U : ℝ} (hL : 0 < L) (hU : 0 ≤ U)
    (hμ : ∀ᵐ z ∂μ, L ≤ ‖z‖ ∧ ‖z‖ ≤ U) {K : ℕ} (hK : 2 ≤ K) :
    Monotone (sumCapacity μ K) :=
  monotone_sumCapacity μ K (sumRates_bddAbove_all μ hL hU hμ hK)

theorem annulus_upper_pos (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {L U : ℝ} (hL : 0 < L) (hμ : ∀ᵐ z ∂μ, L ≤ ‖z‖ ∧ ‖z‖ ≤ U) : 0 < U := by
  obtain ⟨z, hz⟩ := hμ.exists
  exact (hL.trans_le hz.1).trans_le hz.2

end CapacityAtlas.Gaussian.Interference
