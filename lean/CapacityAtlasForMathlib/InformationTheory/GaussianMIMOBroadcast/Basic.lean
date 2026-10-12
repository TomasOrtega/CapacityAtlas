/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx n : ℕ} {rx : Fin K → ℕ}

theorem messageCountProduct_pos (c : Code K tx rx n) :
    0 < ∏ i, (c.messages i : ℝ) := by
  exact Finset.prod_pos fun i _ ↦ Nat.cast_pos.mpr (c.messages_pos i)

theorem card_messages (c : Code K tx rx n) :
    (Fintype.card ((i : Fin K) → Fin (c.messages i)) : ℝ) =
      ∏ i, (c.messages i : ℝ) := by
  simp [Fintype.card_pi]

theorem error_nonneg
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) : 0 ≤ error H N c := by
  unfold error
  positivity

theorem error_le_one
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) : error H N c ≤ 1 := by
  unfold error
  calc
    _ ≤ (∏ i, (c.messages i : ℝ))⁻¹ *
        ∑ _m : (i : Fin K) → Fin (c.messages i), (1 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (messageCountProduct_pos c).le)
      exact Finset.sum_le_sum fun _ _ ↦ measureReal_le_one
    _ = 1 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, card_messages]
      exact inv_mul_cancel₀ (messageCountProduct_pos c).ne'

/-- Receiver error uses the same uniform message tuple and block noise law as joint error. -/
noncomputable def receiverError
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) (i : Fin K) : ℝ :=
  (∏ j, (c.messages j : ℝ))⁻¹ * ∑ m,
    ((blockNoise N n) {z | (c.decode i).apply (output H (c.encode m) z i) ≠ m i}).toReal

theorem receiverError_nonneg
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) (i : Fin K) : 0 ≤ receiverError H N c i := by
  unfold receiverError
  positivity

theorem receiverError_le_error
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) (i : Fin K) : receiverError H N c i ≤ error H N c := by
  unfold receiverError error
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (messageCountProduct_pos c).le)
  apply Finset.sum_le_sum
  intro m _
  exact measureReal_mono fun z hz ↦ ⟨i, hz⟩

theorem error_le_sum_receiverError
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) : error H N c ≤ ∑ i, receiverError H N c i := by
  unfold error receiverError
  rw [← Finset.mul_sum, Finset.sum_comm]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (messageCountProduct_pos c).le)
  apply Finset.sum_le_sum
  intro m _
  simpa only [errorEvent, Set.setOf_exists, measureReal_def] using
    measureReal_iUnion_fintype_le (μ := blockNoise N n)
      (fun i ↦ {z | (c.decode i).apply (output H (c.encode m) z i) ≠ m i})

/-- A single message at every receiver, transmitted without energy. -/
def silentCode (K tx : ℕ) (rx : Fin K → ℕ) (n : ℕ) : Code K tx rx n where
  messages _ := 1
  messages_pos _ := Nat.zero_lt_one
  encode _ _ := 0
  decode _ := {
    apply := fun _ ↦ 0
    measurable_fiber := fun m ↦ by
      have hm : m = 0 := Subsingleton.elim _ _
      simp [hm] }

theorem silentCode_powerAdmissible {P : ℝ} (hP : 0 ≤ P) :
    PowerAdmissible P (silentCode K tx rx n) := by
  simp [PowerAdmissible, silentCode, mul_nonneg (Nat.cast_nonneg n) hP]

theorem silentCode_error
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ) :
    error H N (silentCode K tx rx n) = 0 := by
  have hevent (m : (i : Fin K) → Fin ((silentCode K tx rx n).messages i)) :
      errorEvent H (silentCode K tx rx n) m = ∅ := by
    ext z
    simp only [errorEvent, silentCode, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
      not_exists, not_not]
    intro i
    exact Subsingleton.elim _ _
  simp [error, hevent]

theorem silentCode_rates : rates (silentCode K tx rx n) = 0 := by
  ext i
  simp [rates, silentCode, Operational.messageRate]

theorem zero_mem_achievableVectorRegion
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    {P : ℝ} (hP : 0 ≤ P) :
    (0 : Fin K → ℝ) ∈ Operational.achievableVectorRegion (Code K tx rx)
      (fun _ c ↦ PowerAdmissible P c) (fun _ c ↦ error H N c) (fun _ c ↦ rates c) := by
  refine ⟨fun _ ↦ le_rfl, fun ε hε ↦ ⟨1, Nat.zero_lt_one, fun n _ ↦ ?_⟩⟩
  refine ⟨silentCode K tx rx n, silentCode_powerAdmissible hP, ?_, ?_⟩
  · simpa only [silentCode_error] using hε.le
  · intro i
    simpa only [silentCode_rates, Pi.zero_apply, zero_sub] using neg_nonpos.mpr hε.le

theorem zero_mem_capacityRegion
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    {P : ℝ} (hP : 0 ≤ P) : (0 : Fin K → ℝ) ∈ capacityRegion H N P :=
  subset_closure (zero_mem_achievableVectorRegion H N hP)

theorem PowerAdmissible.mono {P P' : ℝ} {c : Code K tx rx n}
    (h : PowerAdmissible P c) (hPP' : P ≤ P') : PowerAdmissible P' c :=
  h.trans (mul_le_mul_of_nonneg_left hPP' (Nat.cast_nonneg n))

theorem capacityRegion_mono
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    {P P' : ℝ} (hPP' : P ≤ P') : capacityRegion H N P ⊆ capacityRegion H N P' := by
  apply closure_mono
  rintro R ⟨hR, hcodes⟩
  refine ⟨hR, fun ε hε ↦ ?_⟩
  obtain ⟨N, hN, hcodes⟩ := hcodes ε hε
  refine ⟨N, hN, fun n hn ↦ ?_⟩
  obtain ⟨c, hP, herror, hrates⟩ := hcodes n hn
  exact ⟨c, hP.mono hPP', herror, hrates⟩

theorem capacityRegion_eq_achievableVectorRegion
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ) (P : ℝ) :
    capacityRegion H N P = Operational.achievableVectorRegion (Code K tx rx)
      (fun _ c ↦ PowerAdmissible P c) (fun _ c ↦ error H N c) (fun _ c ↦ rates c) :=
  Operational.closure_achievableVectorRegion _ _ _ _

theorem isClosed_capacityRegion
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ) (P : ℝ) :
    IsClosed (capacityRegion H N P) := isClosed_closure

theorem capacityRegion_nonneg
    {H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ}
    {N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ}
    {P : ℝ} {R : Fin K → ℝ} (hR : R ∈ capacityRegion H N P) (i : Fin K) : 0 ≤ R i := by
  rw [capacityRegion_eq_achievableVectorRegion] at hR
  exact hR.1 i

theorem capacityRegion_downward
    {H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ}
    {N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ}
    {P : ℝ} {lower upper : Fin K → ℝ}
    (hupper : upper ∈ capacityRegion H N P) (hlower : ∀ i, 0 ≤ lower i)
    (hle : ∀ i, lower i ≤ upper i) : lower ∈ capacityRegion H N P := by
  rw [capacityRegion_eq_achievableVectorRegion] at hupper ⊢
  exact Operational.achievableVectorRegion_downward hupper hlower hle

end CapacityAtlas.Gaussian.MIMOBroadcast
