/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.Basic

namespace CapacityAtlas.ConfidentialBroadcast

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

theorem capacityRegion_downward (W : FiniteBroadcastChannel X Y Z)
    {lower upper : RatePair} (hupper : upper ∈ capacityRegion W)
    (hcommon : 0 ≤ lower.1) (hsecret : 0 ≤ lower.2)
    (hleCommon : lower.1 ≤ upper.1) (hleSecret : lower.2 ≤ upper.2) :
    lower ∈ capacityRegion W := by
  refine ⟨hcommon, hsecret, fun ε hε ↦ ?_⟩
  obtain ⟨N, hN, hcodes⟩ := hupper.2.2 ε hε
  refine ⟨N, hN, fun n hn ↦ ?_⟩
  obtain ⟨c, hc, he, hr₀, hr₁⟩ := hcodes n hn
  exact ⟨c, hc, he, (sub_le_sub_right hleCommon ε).trans hr₀,
    (sub_le_sub_right hleSecret ε).trans hr₁⟩

theorem isClosed_capacityRegion (W : FiniteBroadcastChannel X Y Z) :
    IsClosed (capacityRegion W) := by
  apply isClosed_of_closure_subset
  intro target ht
  have hcommon : 0 ≤ target.1 :=
    closure_minimal (fun _ hr ↦ hr.1)
      (isClosed_le continuous_const continuous_fst) ht
  have hsecret : 0 ≤ target.2 :=
    closure_minimal (fun _ hr ↦ hr.2.1)
      (isClosed_le continuous_const continuous_snd) ht
  refine ⟨hcommon, hsecret, fun ε hε ↦ ?_⟩
  obtain ⟨nearby, hnearby, hdist⟩ :=
    Metric.mem_closure_iff.mp ht (ε / 2) (half_pos hε)
  obtain ⟨N, hN, hcodes⟩ := hnearby.2.2 (ε / 2) (half_pos hε)
  refine ⟨N, hN, fun n hn ↦ ?_⟩
  obtain ⟨c, hc, he, hr₀, hr₁⟩ := hcodes n hn
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hdist
  have hd₀ := (abs_lt.mp hdist.1).2
  have hd₁ := (abs_lt.mp hdist.2).2
  exact ⟨c, hc, he.trans (by linarith), by linarith, by linarith⟩

theorem auxiliaryRegion_subset_informationRegion (W : FiniteBroadcastChannel X Y Z) :
    auxiliaryRegion W ⊆ informationRegion W := subset_closure

theorem isClosed_informationRegion (W : FiniteBroadcastChannel X Y Z) :
    IsClosed (informationRegion W) := isClosed_closure

theorem informationRegion_nonnegative (W : FiniteBroadcastChannel X Y Z)
    {r : RatePair} (hr : r ∈ informationRegion W) : 0 ≤ r.1 ∧ 0 ≤ r.2 := by
  exact ⟨closure_minimal (fun _ h ↦ h.1)
      (isClosed_le continuous_const continuous_fst) hr,
    closure_minimal (fun _ h ↦ h.2.1)
      (isClosed_le continuous_const continuous_snd) hr⟩

end CapacityAtlas.ConfidentialBroadcast
