/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.Asymptotics
import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.EnsembleCodeBounds

open Filter

namespace CapacityAtlas.ConfidentialBroadcast

open FiniteChannel SuperpositionCode

variable {U V Y Z : Type*} [Fintype U] [Fintype V] [Fintype Y] [Fintype Z]

theorem rounded_common_bound_tendsto (W : FiniteChannel V Y)
    (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ)
    (hgap : r = 0 ∨ r * Real.log 2 + δ < (W.comp (ofRows q)).mutualInformation p) :
    Tendsto (fun n ↦ commonErrorBound W p q n (messageCountAtRate r n) δ) atTop (nhds 0) := by
  rcases hgap with rfl | hgap
  · simpa only [messageCountAtRate_zero, commonErrorBound, if_pos] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0))
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (commonCodingBound_tendsto_zero W p q hr hδ hgap)
    · intro n
      dsimp [commonErrorBound]
      split_ifs
      · rfl
      · exact commonCodingBound_nonnegative W p q _ _ δ
    · intro n
      dsimp [commonErrorBound]
      split_ifs
      · exact commonCodingBound_nonnegative W p q _ _ δ
      · rfl

theorem rounded_satellite_bound_tendsto (W : FiniteChannel V Y)
    (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    {r s δ : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hδ : 0 < δ)
    (hgap : (r + s) * Real.log 2 + δ < conditionalMean W p q) :
    Tendsto (fun n ↦ satelliteErrorBound W p q n
      (messageCountAtRate r n) (messageCountAtRate s n) δ) atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (conditionalCodingBound_product_tendsto_zero W p q hr hs hδ hgap)
  · intro n
    dsimp [satelliteErrorBound]
    split_ifs
    · rfl
    · exact conditionalCodingBound_nonnegative W p q _ _ δ
  · intro n
    dsimp [satelliteErrorBound]
    split_ifs
    · exact conditionalCodingBound_nonnegative W p q _ _ δ
    · rfl

theorem messageCountAtRate_ne_one {r : ℝ} (hr : 0 < r) {n : ℕ} (hn : 0 < n) :
    messageCountAtRate r n ≠ 1 := by
  intro h
  have hl := targetRate_le_rateOfMessageCountAtRate r hn
  simp only [h, Nat.cast_one, Real.logb_one, zero_div] at hl
  linarith

theorem rounded_coding_bound_tendsto (W : FiniteBroadcastChannel V Y Z)
    (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    {r₀ r₁ s δ : ℝ} (hr₀ : 0 ≤ r₀) (hr₁ : 0 < r₁) (hs : 0 ≤ s) (hδ : 0 < δ)
    (hy : r₀ = 0 ∨ r₀ * Real.log 2 + δ < (W.receiver₁.comp (ofRows q)).mutualInformation p)
    (hz : r₀ = 0 ∨ r₀ * Real.log 2 + δ < (W.receiver₂.comp (ofRows q)).mutualInformation p)
    (hsecret : (r₁ + s) * Real.log 2 + δ < conditionalMean W.receiver₁ p q)
    (hseed : (s = 0 ∧ conditionalMean W.receiver₂ p q = 0) ∨
      s * Real.log 2 + δ < conditionalMean W.receiver₂ p q) :
    Tendsto (fun n ↦ finiteCodingBound W p q n (messageCountAtRate r₀ n)
      (messageCountAtRate r₁ n) (messageCountAtRate s n) δ)
      atTop (nhds (conditionalMean W.receiver₂ p q / Real.log 2 - s)) := by
  have hY := rounded_common_bound_tendsto W.receiver₁ p q hr₀ hδ hy
  have hZ := rounded_common_bound_tendsto W.receiver₂ p q hr₀ hδ hz
  have hS := rounded_satellite_bound_tendsto W.receiver₁ p q hr₁.le hs hδ hsecret
  have hL : Tendsto (fun n ↦ seedLeakageBound W.receiver₂ p q n (messageCountAtRate s n) δ)
      atTop (nhds (conditionalMean W.receiver₂ p q / Real.log 2 - s)) := by
    rcases hseed with ⟨rfl, hzero⟩ | hseed
    · simpa only [messageCountAtRate_zero, hzero, zero_div, sub_zero] using
        seedLeakageBound_one_tendsto_zero W.receiver₂ p q δ hzero
    · exact seedLeakageBound_tendsto W.receiver₂ p q hs hδ hseed
  have h := ((hY.add hZ).add hS).add hL
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  simp only [finiteCodingBound, if_neg (messageCountAtRate_ne_one hr₁ hn),
    leakageBound, seedLeakageBound]

theorem common_only_bound_tendsto (W : FiniteBroadcastChannel V Y Z)
    (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ)
    (hy : r = 0 ∨ r * Real.log 2 + δ < (W.receiver₁.comp (ofRows q)).mutualInformation p)
    (hz : r = 0 ∨ r * Real.log 2 + δ < (W.receiver₂.comp (ofRows q)).mutualInformation p) :
    Tendsto (fun n ↦ finiteCodingBound W p q n (messageCountAtRate r n) 1 1 δ)
      atTop (nhds 0) := by
  have h := (rounded_common_bound_tendsto W.receiver₁ p q hr hδ hy).add
    (rounded_common_bound_tendsto W.receiver₂ p q hr hδ hz)
  simpa only [finiteCodingBound, satelliteErrorBound, one_mul, if_pos, add_zero] using h

theorem codes_of_bound_limit (W : FiniteBroadcastChannel V Y Z)
    (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    {r₀ r₁ δ limit ε : ℝ} (hδ : 0 < δ) (hε : limit < ε)
    (seeds : ℕ → ℕ) (hseeds : ∀ n, 0 < seeds n)
    (hlim : Tendsto (fun n ↦ finiteCodingBound W p q n (messageCountAtRate r₀ n)
      (messageCountAtRate r₁ n) (seeds n) δ) atTop (nhds limit)) :
    ∃ N : ℕ, 0 < N ∧ ∀ n, N ≤ n → ∃ c : Code W n,
      c.defect ≤ ε ∧ r₀ ≤ c.rates.1 ∧ r₁ ≤ c.rates.2 := by
  have hevent := (tendsto_order.1 hlim).2 ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨max 1 N, by omega, fun n hn ↦ ?_⟩
  have hn' : 0 < n := by omega
  letI : NeZero (messageCountAtRate r₀ n) := ⟨(messageCountAtRate_pos r₀ n).ne'⟩
  letI : NeZero (messageCountAtRate r₁ n) := ⟨(messageCountAtRate_pos r₁ n).ne'⟩
  letI : NeZero (seeds n) := ⟨(hseeds n).ne'⟩
  obtain ⟨c, hc₀, hc₁, hc⟩ := exists_code_defect_le (C := messageCountAtRate r₀ n)
    (S := messageCountAtRate r₁ n) (L := seeds n) W p q hn' hδ
  refine ⟨c, hc.trans (hN n (by omega)).le, ?_, ?_⟩
  · simpa only [Code.rates, Operational.messageRate, hc₀] using
      targetRate_le_rateOfMessageCountAtRate r₀ hn'
  · simpa only [Code.rates, Operational.messageRate, hc₁] using
      targetRate_le_rateOfMessageCountAtRate r₁ hn'

end CapacityAtlas.ConfidentialBroadcast
