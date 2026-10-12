/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.BlockBounds

open scoped BigOperators
open Filter

namespace CapacityAtlas.FiniteChannel

@[capacity_shared_api]
theorem messageCountAtRate_zero (n : ℕ) : messageCountAtRate 0 n = 1 := by
  simp [messageCountAtRate]

@[capacity_shared_api]
theorem messageCountAtRate_le (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    (messageCountAtRate r n : ℝ) ≤ 2 * Real.exp ((n : ℝ) * r * Real.log 2) :=
  natCeil_exp_le_two_mul_exp (by positivity)

@[capacity_shared_api]
theorem messageRate_messageCountAtRate_le {r : ℝ} (hr : 0 ≤ r) {n : ℕ} (hn : 0 < n) :
    Operational.messageRate (messageCountAtRate r n) n ≤ r + 1 / (n : ℝ) := by
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : (0 : ℝ) < messageCountAtRate r n := by exact_mod_cast messageCountAtRate_pos r n
  have hlog := Real.log_le_log hm (messageCountAtRate_le r hr n)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] at hlog
  unfold Operational.messageRate
  rw [Real.logb, div_div, div_le_iff₀ (mul_pos hlog₂ hn')]
  calc
    Real.log (messageCountAtRate r n) ≤ Real.log 2 + (n : ℝ) * r * Real.log 2 := hlog
    _ = (r + 1 / (n : ℝ)) * (Real.log 2 * (n : ℝ)) := by field_simp; ring

@[capacity_shared_api]
theorem messageRate_messageCountAtRate_tendsto {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun n ↦ Operational.messageRate (messageCountAtRate r n) n) atTop (nhds r) := by
  have hu : Tendsto (fun n : ℕ ↦ r + 1 / (n : ℝ)) atTop (nhds r) := by
    simpa using tendsto_const_nhds.add
      (tendsto_natCast_atTop_atTop.const_div_atTop (1 : ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact targetRate_le_rateOfMessageCountAtRate r hn
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact messageRate_messageCountAtRate_le hr hn

@[capacity_shared_api]
theorem messageCountAtRate_product_le {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (n : ℕ) :
    ((messageCountAtRate r n * messageCountAtRate s n : ℕ) : ℝ) ≤
      4 * Real.exp ((n : ℝ) * (r + s) * Real.log 2) := by
  rw [Nat.cast_mul]
  calc
    _ ≤ (2 * Real.exp ((n : ℝ) * r * Real.log 2)) *
        (2 * Real.exp ((n : ℝ) * s * Real.log 2)) :=
      mul_le_mul (messageCountAtRate_le r hr n) (messageCountAtRate_le s hs n)
        (Nat.cast_nonneg _) (by positivity)
    _ = _ := by
      rw [show (n : ℝ) * (r + s) * Real.log 2 =
        (n : ℝ) * r * Real.log 2 + (n : ℝ) * s * Real.log 2 by ring, Real.exp_add]
      ring

end CapacityAtlas.FiniteChannel

namespace CapacityAtlas.ConfidentialBroadcast

theorem packing_bound_tendsto_zero {μ variance r δ coefficient : ℝ}
    (hv : 0 ≤ variance) (hδ : 0 < δ) (hgap : r * Real.log 2 + δ < μ)
    (counts : ℕ → ℕ)
    (hcounts : ∀ n, (counts n : ℝ) ≤ coefficient * Real.exp ((n : ℝ) * r * Real.log 2)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * variance / (((n : ℝ) * δ) ^ 2) +
      (counts n : ℝ) * Real.exp (-((n : ℝ) * μ - (n : ℝ) * δ))) atTop (nhds 0) := by
  let gap := μ - δ - r * Real.log 2
  have hgap' : 0 < gap := by dsimp [gap]; linarith
  have hpoly : Tendsto (fun n : ℕ ↦ (n : ℝ) * variance / (((n : ℝ) * δ) ^ 2))
      atTop (nhds 0) := by
    apply (tendsto_natCast_atTop_atTop.const_div_atTop (variance / δ ^ 2)).congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp [hn', hδ.ne']
  have hexp : Tendsto (fun n : ℕ ↦ Real.exp (-((n : ℝ) * gap))) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (tendsto_natCast_atTop_atTop.atTop_mul_const hgap'))
  have hup : Tendsto (fun n : ℕ ↦ (n : ℝ) * variance / (((n : ℝ) * δ) ^ 2) +
      coefficient * Real.exp (-((n : ℝ) * gap))) atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using hpoly.add (hexp.const_mul coefficient)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
  · intro n
    positivity
  · intro n
    apply add_le_add le_rfl
    calc
      _ ≤ (coefficient * Real.exp ((n : ℝ) * r * Real.log 2)) *
          Real.exp (-((n : ℝ) * μ - (n : ℝ) * δ)) :=
        mul_le_mul_of_nonneg_right (hcounts n) (Real.exp_pos _).le
      _ = _ := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        dsimp [gap]
        ring

variable {U V Y : Type*} [Fintype U] [Fintype V] [Fintype Y]

theorem conditionalCodingBound_tendsto_zero (W : FiniteChannel V Y)
    (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ)
    (hgap : r * Real.log 2 + δ < conditionalMean W p q) :
    Tendsto (fun n ↦ conditionalCodingBound W p q n (FiniteChannel.messageCountAtRate r n) δ)
      atTop (nhds 0) :=
  packing_bound_tendsto_zero (conditionalVariance_nonnegative W p q) hδ hgap _
    (FiniteChannel.messageCountAtRate_le r hr)

theorem conditionalCodingBound_product_tendsto_zero (W : FiniteChannel V Y)
    (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    {r s δ : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hδ : 0 < δ)
    (hgap : (r + s) * Real.log 2 + δ < conditionalMean W p q) :
    Tendsto (fun n ↦ conditionalCodingBound W p q n
      (FiniteChannel.messageCountAtRate r n * FiniteChannel.messageCountAtRate s n) δ)
      atTop (nhds 0) :=
  packing_bound_tendsto_zero (conditionalVariance_nonnegative W p q) hδ hgap _
    (FiniteChannel.messageCountAtRate_product_le hr hs)

theorem commonCodingBound_tendsto_zero (W : FiniteChannel V Y)
    (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ)
    (hgap : r * Real.log 2 + δ < (W.comp (FiniteChannel.ofRows q)).mutualInformation p) :
    Tendsto (fun n ↦ commonCodingBound W p q n (FiniteChannel.messageCountAtRate r n) δ)
      atTop (nhds 0) :=
  packing_bound_tendsto_zero ((W.comp (FiniteChannel.ofRows q)).informationVariance_nonnegative p)
    hδ hgap _ (FiniteChannel.messageCountAtRate_le r hr)

noncomputable def seedLeakageBound (W : FiniteChannel V Y)
    (p : FiniteDistribution U) (q : U → FiniteDistribution V) (n seeds : ℕ) (δ : ℝ) : ℝ :=
  ((n : ℝ) * (conditionalMean W p q / Real.log 2) - Real.log seeds / Real.log 2 + 1 +
    conditionalCodingBound W p q n seeds δ * (Real.log seeds / Real.log 2)) / n

theorem seedLeakageBound_tendsto (W : FiniteChannel V Y)
    (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ)
    (hgap : r * Real.log 2 + δ < conditionalMean W p q) :
    Tendsto (fun n ↦ seedLeakageBound W p q n (FiniteChannel.messageCountAtRate r n) δ)
      atTop (nhds (conditionalMean W p q / Real.log 2 - r)) := by
  have hrate := FiniteChannel.messageRate_messageCountAtRate_tendsto hr
  have hpack := conditionalCodingBound_tendsto_zero W p q hr hδ hgap
  have h := (((tendsto_const_nhds (x := conditionalMean W p q / Real.log 2)).sub hrate).add
    (tendsto_natCast_atTop_atTop.const_div_atTop (1 : ℝ))).add (hpack.mul hrate)
  simp only [zero_mul, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold seedLeakageBound Operational.messageRate
  rw [Real.logb]
  field_simp

theorem seedLeakageBound_one_tendsto_zero (W : FiniteChannel V Y)
    (p : FiniteDistribution U) (q : U → FiniteDistribution V) (δ : ℝ)
    (hzero : conditionalMean W p q = 0) :
    Tendsto (fun n ↦ seedLeakageBound W p q n 1 δ) atTop (nhds 0) := by
  simpa only [seedLeakageBound, hzero, zero_div, mul_zero, Nat.cast_one,
    Real.log_one, sub_zero, zero_add, add_zero] using
    tendsto_natCast_atTop_atTop.const_div_atTop (1 : ℝ)

end CapacityAtlas.ConfidentialBroadcast
