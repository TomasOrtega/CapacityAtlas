/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.Achievability

open scoped BigOperators

namespace CapacityAtlas.ConfidentialBroadcast

private theorem lowered_rate_properties {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    0 ≤ max 0 (r - ε / 2) ∧ max 0 (r - ε / 2) ≤ r ∧
      |max 0 (r - ε / 2) - r| < ε ∧
      (max 0 (r - ε / 2) = 0 ∨ max 0 (r - ε / 2) < r) := by
  have hnonneg : 0 ≤ max 0 (r - ε / 2) := le_max_left _ _
  have hupper : max 0 (r - ε / 2) ≤ r := max_le hr (by linarith)
  have hlower := le_max_right 0 (r - ε / 2)
  refine ⟨hnonneg, hupper, abs_lt.mpr ⟨by linarith, by linarith⟩, ?_⟩
  rcases le_total 0 (r - ε / 2) with h | h
  · exact Or.inr (by rw [max_eq_right h]; linarith)
  · exact Or.inl (max_eq_left h)

variable {U V X Y Z : Type*} [Fintype U] [Fintype V] [Fintype X] [Fintype Y] [Fintype Z]

theorem superposition_rates_achievable (W : FiniteBroadcastChannel V Y Z)
    (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    {r₀ r₁ : ℝ} (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁)
    (hy : r₀ ≤ (W.receiver₁.comp (FiniteChannel.ofRows q)).mutualInformationBits p)
    (hz : r₀ ≤ (W.receiver₂.comp (FiniteChannel.ofRows q)).mutualInformationBits p)
    (hs : r₁ ≤ conditionalMean W.receiver₁ p q / Real.log 2 -
      conditionalMean W.receiver₂ p q / Real.log 2) :
    (r₀, r₁) ∈ capacityRegion W := by
  apply (isClosed_capacityRegion W).closure_subset
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨ha₀, _, hd₀, hlt₀⟩ := lowered_rate_properties hr₀ hε
  obtain ⟨ha₁, _, hd₁, hlt₁⟩ := lowered_rate_properties hr₁ hε
  have hay := hlt₀.imp_right (fun h ↦ h.trans_le hy)
  have haz := hlt₀.imp_right (fun h ↦ h.trans_le hz)
  refine ⟨(max 0 (r₀ - ε / 2), max 0 (r₁ - ε / 2)), ?_, ?_⟩
  · by_cases hzero : max 0 (r₁ - ε / 2) = 0
    · rw [hzero]
      exact common_only_achievable W p q ha₀ hay haz
    · exact secret_interior_achievable W p q ha₀
        (lt_of_le_of_ne ha₁ (Ne.symm hzero)) hay haz
        ((hlt₁.resolve_left hzero).trans_le hs)
  · rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff, abs_sub_comm r₀, abs_sub_comm r₁]
    exact ⟨hd₀, hd₁⟩

theorem auxiliaryRegion_subset_capacityRegion (W : FiniteBroadcastChannel X Y Z) :
    auxiliaryRegion W ⊆ capacityRegion W := by
  classical
  intro r hr
  rcases hr with ⟨hr₀, hr₁, u, v, p, P, hy, hz, hs⟩
  let q := p.conditionalRows
  let p₀ := p.map Prod.fst
  have hjoint : p₀.joint q = p := p.joint_conditionalRows
  have hy' := auxiliary_information_eq_composed p₀ q P W.receiver₁
  have hz' := auxiliary_information_eq_composed p₀ q P W.receiver₂
  have hsy := auxiliary_conditional_eq_average p₀ q P W.receiver₁
  have hsz := auxiliary_conditional_eq_average p₀ q P W.receiver₂
  rw [hjoint] at hy' hz' hsy hsz
  apply capacityRegion_prefixed_subset W P
  apply superposition_rates_achievable (prefixed W P) p₀ q hr₀ hr₁
  · exact hy.trans_eq hy'
  · exact hz.trans_eq hz'
  · rw [hsy, hsz] at hs
    simpa only [prefixed, conditionalMean, FiniteChannel.mutualInformationBits,
      Finset.sum_div, mul_div_assoc] using hs

theorem informationRegion_subset_capacityRegion (W : FiniteBroadcastChannel X Y Z) :
    informationRegion W ⊆ capacityRegion W :=
  closure_minimal (auxiliaryRegion_subset_capacityRegion W) (isClosed_capacityRegion W)

end CapacityAtlas.ConfidentialBroadcast
