/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.Fano

open scoped BigOperators

namespace CapacityAtlas.ConfidentialBroadcast.Code

open FiniteInformation

variable {X Y Z O : Type*} [Fintype X] [Fintype Y] [Fintype Z] [Fintype O]
    {W : FiniteBroadcastChannel X Y Z} {n : ℕ}

/-- The independent messages stay independent in either receiver's joint law. -/
theorem secret_common_independent (c : Code W n) (V : FiniteChannel X O) :
    information (c.joint V) (fun a ↦ a.1.2) (fun a ↦ a.1.1) = 0 := by
  classical
  letI : Nonempty (Fin c.commonCount) := Fin.pos_iff_nonempty.mp c.commonCount_pos
  letI : Nonempty (Fin c.secretCount) := Fin.pos_iff_nonempty.mp c.secretCount_pos
  have hu : c.messages = independent (FiniteDistribution.uniform (Fin c.commonCount))
      (FiniteDistribution.uniform (Fin c.secretCount)) := by
    ext a
    simp [messages, independent, FiniteInformation.joint,
      FiniteDistribution.joint_apply, FiniteChannel.rowDistribution_ofRows,
      Fintype.card_prod, Nat.cast_mul, mul_inv_rev, mul_comm]
  have hm := information_map (c.joint V) Prod.fst Prod.snd Prod.fst
  simp only [Function.comp_def] at hm
  rw [← hm, c.joint_pair_uniform, information_comm, hu, information_independent]

/-- Reliability and public-message decoding convert weak secrecy to a conditional bound. -/
theorem secret_information_bound (c : Code W n) :
    (1 - c.error) * (Real.log c.secretCount / Real.log 2) -
        c.error * (Real.log c.commonCount / Real.log 2) ≤
      conditional (c.joint W.receiver₁) (fun a ↦ a.1.2) Prod.snd (fun a ↦ a.1.1) -
      conditional (c.joint W.receiver₂) (fun a ↦ a.1.2) Prod.snd (fun a ↦ a.1.1) +
      information (c.joint W.receiver₂) (fun a ↦ a.1.2) Prod.snd + 2 := by
  have hf := c.secret_fano_with_common
  rw [information_chain_rule, c.secret_common_independent, zero_add] at hf
  have hl := conditional_le_information_add_conditionalEntropy (c.joint W.receiver₂)
    (fun a ↦ a.1.2) Prod.snd (fun a ↦ a.1.1) (c.secret_common_independent _)
  have hc := c.common_conditionalEntropy_fano
  linarith

theorem secret_rate_information_bound (c : Code W n) :
    (1 - c.error) * c.rates.2 - c.error * c.rates.1 ≤
      (conditional (c.joint W.receiver₁) (fun a ↦ a.1.2) Prod.snd (fun a ↦ a.1.1) -
      conditional (c.joint W.receiver₂) (fun a ↦ a.1.2) Prod.snd (fun a ↦ a.1.1)) / n +
      c.leakage + 2 / (n : ℝ) := by
  have h := div_le_div_of_nonneg_right c.secret_information_bound
    (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simpa only [rates, Operational.messageRate, Real.logb, sub_div, add_div,
    mul_div_assoc, leakage] using h

theorem rates_nonneg (c : Code W n) : 0 ≤ c.rates.1 ∧ 0 ≤ c.rates.2 := by
  constructor
  · exact div_nonneg (div_nonneg
      (Real.log_nonneg (by exact_mod_cast c.commonCount_pos))
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le) (Nat.cast_nonneg n)
  · exact div_nonneg (div_nonneg
      (Real.log_nonneg (by exact_mod_cast c.secretCount_pos))
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le) (Nat.cast_nonneg n)

/-- A bounded-error code has a uniformly bounded sum rate. -/
theorem sum_rate_le (c : Code W n) (hn : 0 < n) (he : c.error ≤ 1 / 2) :
    c.rates.1 + c.rates.2 ≤ 2 * (|Real.log (Fintype.card Y) / Real.log 2| + 1) := by
  have hf := c.pair_fano
  have hi := information_le_entropy_right (c.joint W.receiver₁) Prod.fst Prod.snd
  have hh := entropy_le_log_card (c.joint W.receiver₁) Prod.snd
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow,
    mul_div_assoc] at hh
  have hfull : (1 - c.error) * (Real.log c.commonCount / Real.log 2 +
      Real.log c.secretCount / Real.log 2) ≤
      (n : ℝ) * (Real.log (Fintype.card Y) / Real.log 2) + 1 := by linarith
  have hdiv := div_le_div_of_nonneg_right hfull (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hrate : (1 - c.error) * (c.rates.1 + c.rates.2) ≤
      Real.log (Fintype.card Y) / Real.log 2 + (n : ℝ)⁻¹ := by
    simpa [rates, Operational.messageRate, Real.logb, add_div, mul_div_assoc, hn0] using hdiv
  have hinv : (n : ℝ)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact_mod_cast hn
  have hr := c.rates_nonneg
  have habs := le_abs_self (Real.log (Fintype.card Y) / Real.log 2)
  nlinarith

end CapacityAtlas.ConfidentialBroadcast.Code

namespace CapacityAtlas.ConfidentialBroadcast

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {W : FiniteBroadcastChannel X Y Z}

/-- Lower nonnegative rates use the same auxiliary distribution and prefix. -/
theorem auxiliaryRegion_downward {r s : RatePair} (hr : r ∈ auxiliaryRegion W)
    (hs : 0 ≤ s.1 ∧ 0 ≤ s.2) (hle : s.1 ≤ r.1 ∧ s.2 ≤ r.2) :
    s ∈ auxiliaryRegion W := by
  obtain ⟨hr₁, hr₂, u, v, p, channelPrefix, h₁, h₂, h₃⟩ := hr
  exact ⟨hs.1, hs.2, u, v, p, channelPrefix,
    hle.1.trans h₁, hle.1.trans h₂, hle.2.trans h₃⟩

/-- Finite-block converse witnesses suffice for the closed operational region. -/
theorem capacityRegion_subset_informationRegion_of_code_bounds
    (hfinite : ∀ (n : ℕ), 0 < n → ∀ (c : Code W n),
      ∃ r ∈ auxiliaryRegion W,
        (1 - c.error) * c.rates.1 ≤ r.1 + (n : ℝ)⁻¹ ∧
        (1 - c.error) * c.rates.2 - c.error * c.rates.1 ≤
          r.2 + c.leakage + 2 / (n : ℝ)) :
    capacityRegion W ⊆ informationRegion W := by
  intro target ht
  change target ∈ closure (auxiliaryRegion W)
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let K : ℝ := 2 * (|Real.log (Fintype.card Y) / Real.log 2| + 1)
  have hK : 0 ≤ K := by positivity
  let δ : ℝ := min (1 / 4) (ε / (4 * (K + 2)))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδquarter : δ ≤ 1 / 4 := min_le_left _ _
  have hδsmall : δ * (K + 2) ≤ ε / 4 := by
    have hb := (le_div_iff₀ (show 0 < 4 * (K + 2) by positivity)).mp
      (show δ ≤ ε / (4 * (K + 2)) from min_le_right _ _)
    nlinarith
  obtain ⟨N, hN, hcodes⟩ := ht.2.2 δ hδ
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt (show 0 < ε / 8 by positivity)
  let n := max N (M + 1)
  have hnN : N ≤ n := le_max_left _ _
  have hnM : M + 1 ≤ n := le_max_right _ _
  have hn : 0 < n := hN.trans_le hnN
  have hinv : (n : ℝ)⁻¹ < ε / 8 := by
    have h := one_div_le_one_div_of_le (show (0 : ℝ) < M + 1 by positivity)
      (show (M : ℝ) + 1 ≤ n by exact_mod_cast hnM)
    have hninv : (n : ℝ)⁻¹ ≤ 1 / (M + 1 : ℝ) := by simpa only [one_div] using h
    exact hninv.trans_lt hM
  obtain ⟨c, _, hc, hrate₁, hrate₂⟩ := hcodes n hnN
  have he : c.error ≤ δ := (le_max_left _ _).trans hc
  have hleak : c.leakage ≤ δ := (le_max_right _ _).trans hc
  have hrates := c.rates_nonneg
  have hsum : c.rates.1 + c.rates.2 ≤ K := c.sum_rate_le hn (by linarith)
  have hcommon : c.rates.1 ≤ K := (le_add_of_nonneg_right hrates.2).trans hsum
  have hecommon := mul_le_mul he hcommon hrates.1 hδ.le
  have hesum := mul_le_mul he hsum (add_nonneg hrates.1 hrates.2) hδ.le
  obtain ⟨r, hr, hc₁, hc₂⟩ := hfinite n hn c
  have hgap₁ : target.1 - r.1 < ε := by
    have haux : target.1 - r.1 ≤ δ * (K + 1) + (n : ℝ)⁻¹ := by nlinarith
    nlinarith
  have hgap₂ : target.2 - r.2 < ε := by
    have haux : target.2 - r.2 ≤ δ * (K + 2) + 2 * (n : ℝ)⁻¹ := by
      rw [div_eq_mul_inv] at hc₂
      nlinarith
    nlinarith
  let q : RatePair := (min target.1 r.1, min target.2 r.2)
  have hq : q ∈ auxiliaryRegion W := auxiliaryRegion_downward hr
    ⟨le_min ht.1 hr.1, le_min ht.2.1 hr.2.1⟩ ⟨min_le_right _ _, min_le_right _ _⟩
  refine ⟨q, hq, ?_⟩
  rw [Prod.dist_eq]
  apply max_lt
  · rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (min_le_left _ _))]
    change target.1 - min target.1 r.1 < ε
    by_cases h : target.1 ≤ r.1
    · simpa only [min_eq_left h, sub_self] using hε
    · simpa only [min_eq_right (le_of_not_ge h)] using hgap₁
  · rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (min_le_left _ _))]
    change target.2 - min target.2 r.2 < ε
    by_cases h : target.2 ≤ r.2
    · simpa only [min_eq_left h, sub_self] using hε
    · simpa only [min_eq_right (le_of_not_ge h)] using hgap₂

end CapacityAtlas.ConfidentialBroadcast
