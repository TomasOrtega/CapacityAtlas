/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.DirectLimits
import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.AuxiliaryLaws
import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.RegionGeometry

open scoped BigOperators

namespace CapacityAtlas.ConfidentialBroadcast

private theorem choose_common_slack {r a b : ℝ}
    (ha : r = 0 ∨ r < a) (hb : r = 0 ∨ r < b) :
    ∃ δ : ℝ, 0 < δ ∧ (r = 0 ∨ r + δ < a) ∧ (r = 0 ∨ r + δ < b) := by
  by_cases hr : r = 0
  · exact ⟨1, by norm_num, Or.inl hr, Or.inl hr⟩
  have ha' : 0 < a - r := sub_pos.mpr (ha.resolve_left hr)
  have hb' : 0 < b - r := sub_pos.mpr (hb.resolve_left hr)
  obtain ⟨δ, hδ, hδ'⟩ := exists_between (lt_min ha' hb')
  exact ⟨δ, hδ, Or.inr (by linarith [(lt_min_iff.mp hδ').1]),
    Or.inr (by linarith [(lt_min_iff.mp hδ').2])⟩

private theorem choose_secret_slack {r₀ r₁ a b y z ε : ℝ}
    (ha : r₀ = 0 ∨ r₀ < a) (hb : r₀ = 0 ∨ r₀ < b)
    (hsecret : r₁ < y - z) (hz : 0 ≤ z) (hε : 0 < ε) :
    ∃ s δ : ℝ, 0 ≤ s ∧ 0 < δ ∧ z - s < ε ∧
      (r₀ = 0 ∨ r₀ + δ < a) ∧ (r₀ = 0 ∨ r₀ + δ < b) ∧
      r₁ + s + δ < y ∧ ((s = 0 ∧ z = 0) ∨ s + δ < z) := by
  let s := max 0 (z - ε / 2)
  have hs : 0 ≤ s := le_max_left _ _
  have hsz : s ≤ z := max_le hz (by linarith)
  have hsmall : z - s < ε := by have := le_max_right 0 (z - ε / 2); dsimp [s]; linarith
  have hslt (hz' : z ≠ 0) : s < z := max_lt (lt_of_le_of_ne hz (Ne.symm hz')) (by linarith)
  let a' := if r₀ = 0 then 1 else a - r₀
  let b' := if r₀ = 0 then 1 else b - r₀
  let z' := if z = 0 then 1 else z - s
  have hap : 0 < a' := by
    dsimp [a']; split_ifs with h
    · norm_num
    · exact sub_pos.mpr (ha.resolve_left h)
  have hbp : 0 < b' := by
    dsimp [b']; split_ifs with h
    · norm_num
    · exact sub_pos.mpr (hb.resolve_left h)
  have hyp : 0 < y - (r₁ + s) := by linarith
  have hzp : 0 < z' := by
    dsimp [z']; split_ifs with h
    · norm_num
    · exact sub_pos.mpr (hslt h)
  obtain ⟨δ, hδ, hδall⟩ := exists_between (lt_min hap (lt_min hbp (lt_min hyp hzp)))
  rcases lt_min_iff.mp hδall with ⟨hδa, hδall⟩
  rcases lt_min_iff.mp hδall with ⟨hδb, hδall⟩
  rcases lt_min_iff.mp hδall with ⟨hδy, hδz⟩
  refine ⟨s, δ, hs, hδ, hsmall, ?_, ?_, by linarith, ?_⟩
  · by_cases h : r₀ = 0
    · exact Or.inl h
    · exact Or.inr (by simp only [a', h, if_false] at hδa; linarith)
  · by_cases h : r₀ = 0
    · exact Or.inl h
    · exact Or.inr (by simp only [b', h, if_false] at hδb; linarith)
  · by_cases h : z = 0
    · exact Or.inl ⟨le_antisymm (by simpa only [h] using hsz) hs, h⟩
    · exact Or.inr (by simp only [z', h, if_false] at hδz; linarith)

variable {U V Y Z : Type*} [Fintype U] [Fintype V] [Fintype Y] [Fintype Z]

theorem conditionalMean_nonnegative (W : FiniteChannel V Y)
    (p : FiniteDistribution U) (q : U → FiniteDistribution V) :
    0 ≤ conditionalMean W p q :=
  Finset.sum_nonneg fun u _ ↦ mul_nonneg (p.nonnegative u) (W.mutualInformation_nonnegative (q u))

private theorem nats_gap {r δ μ : ℝ} (h : r + δ < μ / Real.log 2) :
    r * Real.log 2 + δ * Real.log 2 < μ := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm := (lt_div_iff₀ hlog).mp h
  nlinarith

theorem common_only_achievable (W : FiniteBroadcastChannel V Y Z)
    (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    {r : ℝ} (hr : 0 ≤ r)
    (hy : r = 0 ∨ r < (W.receiver₁.comp (FiniteChannel.ofRows q)).mutualInformationBits p)
    (hz : r = 0 ∨ r < (W.receiver₂.comp (FiniteChannel.ofRows q)).mutualInformationBits p) :
    (r, 0) ∈ capacityRegion W := by
  obtain ⟨δ, hδ, hyδ, hzδ⟩ := choose_common_slack hy hz
  have hδn : 0 < δ * Real.log 2 := mul_pos hδ (Real.log_pos (by norm_num))
  have hlim := common_only_bound_tendsto W p q hr hδn
    (hyδ.imp_right (fun h ↦ nats_gap h)) (hzδ.imp_right (fun h ↦ nats_gap h))
  refine ⟨hr, le_rfl, fun ε hε ↦ ?_⟩
  have hlim' : Filter.Tendsto (fun n ↦ SuperpositionCode.finiteCodingBound W p q n
      (FiniteChannel.messageCountAtRate r n) (FiniteChannel.messageCountAtRate 0 n) 1
      (δ * Real.log 2)) Filter.atTop (nhds 0) := by
    simpa only [FiniteChannel.messageCountAtRate_zero] using hlim
  obtain ⟨N, hN, hcodes⟩ := codes_of_bound_limit W p q hδn hε (fun _ ↦ 1) (fun _ ↦ by omega) hlim'
  refine ⟨N, hN, fun n hn ↦ ?_⟩
  obtain ⟨c, hc, hc₀, hc₁⟩ := hcodes n hn
  exact ⟨c, trivial, hc, by dsimp; linarith, by dsimp; linarith⟩

theorem secret_interior_achievable (W : FiniteBroadcastChannel V Y Z)
    (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    {r₀ r₁ : ℝ} (hr₀ : 0 ≤ r₀) (hr₁ : 0 < r₁)
    (hy : r₀ = 0 ∨ r₀ < (W.receiver₁.comp (FiniteChannel.ofRows q)).mutualInformationBits p)
    (hz : r₀ = 0 ∨ r₀ < (W.receiver₂.comp (FiniteChannel.ofRows q)).mutualInformationBits p)
    (hsecret : r₁ < conditionalMean W.receiver₁ p q / Real.log 2 -
      conditionalMean W.receiver₂ p q / Real.log 2) :
    (r₀, r₁) ∈ capacityRegion W := by
  refine ⟨hr₀, hr₁.le, fun ε hε ↦ ?_⟩
  have hz0 := div_nonneg (conditionalMean_nonnegative W.receiver₂ p q)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  obtain ⟨s, δ, hs, hδ, hsmall, hyδ, hzδ, hsecδ, hseedδ⟩ :=
    choose_secret_slack hy hz hsecret hz0 hε
  have hδn : 0 < δ * Real.log 2 := mul_pos hδ (Real.log_pos (by norm_num))
  have hseed : (s = 0 ∧ conditionalMean W.receiver₂ p q = 0) ∨
      s * Real.log 2 + δ * Real.log 2 < conditionalMean W.receiver₂ p q := by
    rcases hseedδ with ⟨hs0, hz0⟩ | hseedδ
    · exact Or.inl ⟨hs0, (div_eq_zero_iff.mp hz0).resolve_right
        (ne_of_gt (Real.log_pos (by norm_num)))⟩
    · exact Or.inr (nats_gap hseedδ)
  have hlim := rounded_coding_bound_tendsto W p q hr₀ hr₁ hs hδn
    (hyδ.imp_right (fun h ↦ nats_gap h)) (hzδ.imp_right (fun h ↦ nats_gap h))
    (nats_gap hsecδ) hseed
  obtain ⟨N, hN, hcodes⟩ := codes_of_bound_limit W p q hδn hsmall
    (FiniteChannel.messageCountAtRate s) (FiniteChannel.messageCountAtRate_pos s) hlim
  refine ⟨N, hN, fun n hn ↦ ?_⟩
  obtain ⟨c, hc, hc₀, hc₁⟩ := hcodes n hn
  exact ⟨c, trivial, hc, by dsimp; linarith, by dsimp; linarith⟩

end CapacityAtlas.ConfidentialBroadcast
