/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.TimeSharingCodes
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

namespace CapacityAtlas.Gaussian.MIMOBroadcast

noncomputable def timeSharingLength (a : ℝ) (n : ℕ) : ℕ := ⌊a * n⌋₊

lemma timeSharingLength_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    timeSharingLength a n ≤ n := by
  have hfloor := Nat.floor_le (mul_nonneg ha (Nat.cast_nonneg n))
  have hab : a * (n : ℝ) ≤ n := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  exact_mod_cast hfloor.trans hab

lemma tendsto_timeSharingLength {a : ℝ} (ha : 0 < a) :
    Tendsto (timeSharingLength a) atTop atTop := tendsto_nat_floor_mul_atTop a ha

lemma tendsto_timeSharingLength_div {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ ↦ (timeSharingLength a n : ℝ) / n) atTop (𝓝 a) :=
  (tendsto_nat_floor_mul_div_atTop ha).comp tendsto_natCast_atTop_atTop

lemma tendsto_timeSharingRemainder {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (fun n : ℕ ↦ n - timeSharingLength a n) atTop atTop := by
  apply tendsto_atTop_mono _ (tendsto_nat_floor_mul_atTop (1 - a) (sub_pos.mpr ha1))
  intro n
  have hf := Nat.floor_le (mul_nonneg ha (Nat.cast_nonneg n))
  have hg := Nat.floor_le (mul_nonneg (sub_nonneg.mpr ha1.le) (Nat.cast_nonneg n))
  have hs : ((n - timeSharingLength a n : ℕ) : ℝ) = n - (timeSharingLength a n : ℝ) :=
    Nat.cast_sub (timeSharingLength_le ha ha1.le n)
  change ⌊(1 - a) * (n : ℝ)⌋₊ ≤ n - timeSharingLength a n
  apply (Nat.cast_le (α := ℝ)).mp
  rw [hs]
  change (⌊(1 - a) * (n : ℝ)⌋₊ : ℝ) ≤ (n : ℝ) - (⌊a * (n : ℝ)⌋₊ : ℝ)
  linarith

lemma tendsto_timeSharingRemainder_div {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Tendsto (fun n : ℕ ↦ ((n - timeSharingLength a n : ℕ) : ℝ) / n) atTop (𝓝 (1 - a)) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_timeSharingLength_div ha)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [Nat.cast_sub (timeSharingLength_le ha ha1 n), sub_div,
    div_self (Nat.cast_ne_zero.mpr (by omega : n ≠ 0))]

variable {K tx : ℕ} {rx : Fin K → ℕ}

/-- Time sharing of actual finite codes proves convexity of the operational region. -/
theorem convex_capacityRegion
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ) (P : ℝ) :
    Convex ℝ (capacityRegion H N P) := by
  intro R hR S hS a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa only [ha0, hb1, zero_smul, one_smul, zero_add] using hS
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simpa only [ha1, hb0, zero_smul, one_smul, add_zero] using hR
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have ha1 : a < 1 := by linarith
  have hbval : 1 - a = b := by linarith
  rw [capacityRegion_eq_achievableVectorRegion] at hR hS ⊢
  refine ⟨fun i ↦ add_nonneg (mul_nonneg ha (hR.1 i)) (mul_nonneg hb (hS.1 i)), fun ε hε ↦ ?_⟩
  obtain ⟨nr, hnr, hcodesR⟩ := hR.2 (ε / 2) (half_pos hε)
  obtain ⟨ns, hns, hcodesS⟩ := hS.2 (ε / 2) (half_pos hε)
  have hp := tendsto_timeSharingLength ha'
  have hq := tendsto_timeSharingRemainder ha ha1
  have hweightsP := tendsto_timeSharingLength_div ha
  have hweightsQ := tendsto_timeSharingRemainder_div ha ha1.le
  rw [hbval] at hweightsQ
  have hrates : ∀ᶠ k : ℕ in atTop, ∀ i : Fin K,
      a * R i + b * S i - ε ≤
        (timeSharingLength a k : ℝ) / k * (R i - ε / 2) +
          ((k - timeSharingLength a k : ℕ) : ℝ) / k * (S i - ε / 2) := by
    apply eventually_all.mpr
    intro i
    have hl := (hweightsP.mul_const (R i - ε / 2)).add
      (hweightsQ.mul_const (S i - ε / 2))
    have hstrict : a * R i + b * S i - ε < a * (R i - ε / 2) + b * (S i - ε / 2) := by
      nlinarith
    exact (hl.eventually (eventually_gt_nhds hstrict)).mono (fun _ h ↦ h.le)
  have hall : ∀ᶠ k : ℕ in atTop, ∃ c : Code K tx rx k,
      PowerAdmissible P c ∧ error H N c ≤ ε ∧ ∀ i, (a • R + b • S) i - ε ≤ rates c i := by
    filter_upwards [hp.eventually (eventually_ge_atTop nr),
      hq.eventually (eventually_ge_atTop ns), hrates] with k hpk hqk hrate
    obtain ⟨c, hc, hec, hrc⟩ := hcodesR _ hpk
    obtain ⟨d, hd, hed, hrd⟩ := hcodesS _ hqk
    have hlen : timeSharingLength a k + (k - timeSharingLength a k) = k :=
      Nat.add_sub_of_le (timeSharingLength_le ha ha1.le k)
    have hcpos : 0 < timeSharingLength a k := hnr.trans_le hpk
    have hdpos : 0 < k - timeSharingLength a k := hns.trans_le hqk
    have herr : error H N (c.concat d) ≤ ε :=
      (c.concat_error_le H N d).trans (by linarith)
    have hr (i : Fin K) : (a • R + b • S) i - ε ≤ rates (c.concat d) i := by
      rw [c.concat_rates d hcpos hdpos i, ← Nat.cast_add, hlen]
      exact (hrate i).trans (add_le_add
        (mul_le_mul_of_nonneg_left (hrc i) (by positivity))
        (mul_le_mul_of_nonneg_left (hrd i) (by positivity)))
    have hex : ∃ e : Code K tx rx (timeSharingLength a k + (k - timeSharingLength a k)),
        PowerAdmissible P e ∧ error H N e ≤ ε ∧ ∀ i, (a • R + b • S) i - ε ≤ rates e i :=
      ⟨c.concat d, c.concat_powerAdmissible d hc hd, herr, hr⟩
    exact hlen ▸ hex
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hall
  exact ⟨max n₀ 1, by omega, fun k hk ↦ hn₀ k (le_trans (le_max_left _ _) hk)⟩

end CapacityAtlas.Gaussian.MIMOBroadcast
