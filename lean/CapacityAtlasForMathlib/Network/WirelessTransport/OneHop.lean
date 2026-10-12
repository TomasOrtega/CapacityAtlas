/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Network.WirelessTransport.Basic

open scoped BigOperators

noncomputable section

namespace CapacityAtlas.WirelessTransport

/-- Any finite feasible collection of direct links can run for the whole interval. -/
theorem oneHop_achievable {n : ℕ} (I : Type) [Fintype I] (tx rx : I → Point)
    (R Δ W : ℝ) (hcard : 2 * Fintype.card I ≤ n) (hW : 0 ≤ W)
    (htx : ∀ i, ‖tx i‖ ≤ R) (hrx : ∀ i, ‖rx i‖ ≤ R)
    (hprotocol : ∀ i j, i ≠ j → (1 + Δ) * dist (tx i) (rx i) ≤ dist (tx j) (rx i)) :
    Achievable n R Δ W (W * ∑ i, dist (tx i) (rx i)) := by
  classical
  let position : I ⊕ I → Point := Sum.elim tx rx
  let P : Pattern (I ⊕ I) position Δ := {
    Link := I
    finiteLink := inferInstance
    sender := Sum.inl
    receiver := Sum.inr
    sender_injective := Sum.inl_injective
    protocol := hprotocol }
  let S : Schedule (I ⊕ I) position Δ W := {
    slots := 1
    bands := 1
    duration := fun _ => 1
    duration_nonneg := fun _ => zero_le_one
    duration_sum := by simp
    bandRate := fun _ => W
    bandRate_nonneg := fun _ => hW
    bandRate_sum := by simp
    pattern := fun _ _ => P }
  have hintegral : ∃ T : ℝ, 0 < T ∧ ∀ _ : I, ∃ k : ℕ, W * T = k := by
    by_cases hz : W = 0
    · exact ⟨1, zero_lt_one, fun _ => ⟨0, by simp [hz]⟩⟩
    · exact ⟨1 / W, by positivity, fun _ => ⟨1, by simp [hz]⟩⟩
  let E : Execution (I ⊕ I) position Δ W := {
    schedule := S
    Packet := I
    finitePacket := inferInstance
    amount := fun _ => W
    amount_nonneg := fun _ => hW
    integralAmounts := hintegral
    destination := Sum.elim Sum.inr Sum.inr
    hops := fun _ => 1
    route := fun i k => if k = 0 then Sum.inl i else Sum.inr i
    delivered := by intro i; simp
    resource := fun i _ => ⟨0, ⟨0, i⟩⟩
    causal := by
      intro i a b hab
      have he : a = b := Subsingleton.elim _ _
      subst b
      exact (lt_irrefl _ hab).elim
    hop_sender := by intro i h; simp [Schedule.sender, S, P, Fin.eq_zero h]
    hop_receiver := by intro i h; simp [Schedule.receiver, S, P]
    load_le := by
      intro r
      rcases r with ⟨s, b, j⟩
      have hs : s = 0 := Subsingleton.elim _ _
      have hb : b = 0 := Subsingleton.elim _ _
      subst s b
      simp only [Fin.sum_univ_one]
      change (∑ x : I, if (⟨0, ⟨0, x⟩⟩ : S.Resource) = ⟨0, ⟨0, j⟩⟩
        then W else 0) ≤ 1 * W
      have heq (x : I) : (⟨0, ⟨0, x⟩⟩ : S.Resource) = ⟨0, ⟨0, j⟩⟩ ↔ x = j := by
        constructor
        · intro h
          exact congrArg (fun r : S.Resource => (r.2.2 : I)) h
        · intro h
          subst x
          rfl
      simp [heq] }
  refine ⟨I ⊕ I, inferInstance, ?_, position, ?_, E, ?_⟩
  · simpa [Fintype.card_sum, two_mul] using hcard
  · intro i
    cases i with
    | inl i => exact htx i
    | inr i => exact hrx i
  · simp [Execution.transportRate, E, position, Finset.mul_sum]

end CapacityAtlas.WirelessTransport
