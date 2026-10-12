/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Network.WirelessTransport.Basic

open scoped BigOperators

namespace CapacityAtlas.WirelessTransport

noncomputable section

def upperConstant (R Δ : ℝ) : ℝ := 2 * (1 + Δ) * R / Δ

theorem upperConstant_nonneg {R Δ : ℝ} (hR : 0 ≤ R) (hΔ : 0 < Δ) :
    0 ≤ upperConstant R Δ := by unfold upperConstant; positivity

namespace Schedule

variable {V : Type} [Fintype V] {position : V → Point} {Δ W R : ℝ}

theorem hopWork_le (S : Schedule V position Δ W) {n : ℕ}
    (hn : Fintype.card V ≤ n) (hR : 0 ≤ R) (hΔ : 0 < Δ) (_hW : 0 ≤ W)
    (hposition : ∀ v, ‖position v‖ ≤ R) :
    ∑ r : S.Resource, S.available r * S.length r ≤
      W * upperConstant R Δ * Real.sqrt n := by
  classical
  let U := upperConstant R Δ * Real.sqrt n
  have hU : 0 ≤ U := mul_nonneg (upperConstant_nonneg hR hΔ) (Real.sqrt_nonneg _)
  have hp (s : Fin S.slots) (b : Fin S.bands) :
      ∑ l : (S.pattern s b).Link,
        dist (position ((S.pattern s b).sender l))
          (position ((S.pattern s b).receiver l)) ≤ U := by
    have hc : Fintype.card (S.pattern s b).Link ≤ n :=
      (Fintype.card_le_of_injective _ (S.pattern s b).sender_injective).trans hn
    exact (sum_linkLength_le _ _ R Δ hR hΔ
      (fun l => hposition ((S.pattern s b).sender l))
      (fun l => hposition ((S.pattern s b).receiver l)) (S.pattern s b).protocol).trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hc))
          (upperConstant_nonneg hR hΔ))
  have hd : 0 ≤ ∑ s, S.duration s := Finset.sum_nonneg fun s _ => S.duration_nonneg s
  have hb : 0 ≤ ∑ b, S.bandRate b := Finset.sum_nonneg fun b _ => S.bandRate_nonneg b
  calc
    ∑ r : S.Resource, S.available r * S.length r =
        ∑ s, ∑ b, S.duration s * S.bandRate b *
          ∑ l : (S.pattern s b).Link,
            dist (position ((S.pattern s b).sender l))
              (position ((S.pattern s b).receiver l)) := by
      simp only [Fintype.sum_sigma, available, length, sender, receiver, Finset.mul_sum]
    _ ≤ ∑ s, ∑ b, S.duration s * S.bandRate b * U := by
      apply Finset.sum_le_sum
      intro s _
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (hp s b)
        (mul_nonneg (S.duration_nonneg s) (S.bandRate_nonneg b))
    _ = (∑ s, S.duration s) * (∑ b, S.bandRate b) * U := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ 1 * W * U := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul S.duration_sum S.bandRate_sum hb (by norm_num)) hU
    _ = W * upperConstant R Δ * Real.sqrt n := by dsimp [U]; ring

end Schedule

namespace Execution

variable {V : Type} {position : V → Point} {Δ W : ℝ}

theorem endpoint_le_hops (E : Execution V position Δ W) (p : E.Packet) :
    dist (position (E.route p 0)) (position (E.route p (E.hops p))) ≤
      ∑ h : Fin (E.hops p), E.schedule.length (E.resource p h) := by
  have ht := dist_le_range_sum_dist (fun k => position (E.route p k)) (E.hops p)
  simpa only [← Fin.sum_univ_eq_sum_range, Schedule.length, E.hop_sender,
    E.hop_receiver] using ht

theorem transportRate_le_hopWork (E : Execution V position Δ W) :
    E.transportRate ≤ ∑ r : E.schedule.Resource,
      E.schedule.available r * E.schedule.length r := by
  classical
  have haccount :
      (∑ p, ∑ h : Fin (E.hops p), E.amount p * E.schedule.length (E.resource p h)) =
      ∑ r : E.schedule.Resource,
        (∑ p, ∑ h : Fin (E.hops p), if E.resource p h = r then E.amount p else 0) *
          E.schedule.length r := by
    simp_rw [Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_comm]
    simp
  calc
    E.transportRate ≤
        ∑ p, E.amount p * ∑ h : Fin (E.hops p), E.schedule.length (E.resource p h) := by
      exact Finset.sum_le_sum fun p _ =>
        mul_le_mul_of_nonneg_left (E.endpoint_le_hops p) (E.amount_nonneg p)
    _ = ∑ p, ∑ h : Fin (E.hops p), E.amount p * E.schedule.length (E.resource p h) := by
      simp only [Finset.mul_sum]
    _ = _ := haccount
    _ ≤ _ := Finset.sum_le_sum fun r _ =>
      mul_le_mul_of_nonneg_right (E.load_le r) dist_nonneg

theorem transportRate_le [Fintype V] (E : Execution V position Δ W) {n : ℕ} {R : ℝ}
    (hn : Fintype.card V ≤ n) (hR : 0 ≤ R) (hΔ : 0 < Δ) (hW : 0 ≤ W)
    (hposition : ∀ v, ‖position v‖ ≤ R) :
    E.transportRate ≤ W * upperConstant R Δ * Real.sqrt n :=
  E.transportRate_le_hopWork.trans (E.schedule.hopWork_le hn hR hΔ hW hposition)

end Execution

theorem achievable_le {n : ℕ} {R Δ W t : ℝ} (ht : Achievable n R Δ W t)
    (hR : 0 ≤ R) (hΔ : 0 < Δ) (hW : 0 ≤ W) :
    t ≤ W * upperConstant R Δ * Real.sqrt n := by
  obtain ⟨V, hV, hn, position, hposition, E, rfl⟩ := ht
  exact E.transportRate_le hn hR hΔ hW hposition

theorem achievable_bddAbove {n : ℕ} {R Δ W : ℝ}
    (hR : 0 ≤ R) (hΔ : 0 < Δ) (hW : 0 ≤ W) :
    BddAbove {t | Achievable n R Δ W t} :=
  ⟨W * upperConstant R Δ * Real.sqrt n, fun _ ht => achievable_le ht hR hΔ hW⟩

theorem Achievable.le_capacity {n : ℕ} {R Δ W t : ℝ} (ht : Achievable n R Δ W t)
    (hR : 0 ≤ R) (hΔ : 0 < Δ) (hW : 0 ≤ W) : t ≤ capacity n R Δ W :=
  le_csSup (achievable_bddAbove hR hΔ hW) ht

theorem zero_achievable (n : ℕ) (R Δ W : ℝ) (hW : 0 ≤ W) :
    Achievable n R Δ W 0 := by
  classical
  let S : Schedule Empty Empty.elim Δ W := {
    slots := 0
    bands := 0
    duration := Fin.elim0
    duration_nonneg := fun s => Fin.elim0 s
    duration_sum := by simp
    bandRate := Fin.elim0
    bandRate_nonneg := fun b => Fin.elim0 b
    bandRate_sum := by simpa using hW
    pattern := fun s => Fin.elim0 s }
  let E : Execution Empty Empty.elim Δ W := {
    schedule := S
    Packet := Empty
    finitePacket := inferInstance
    amount := Empty.elim
    amount_nonneg := fun p => p.elim
    integralAmounts := ⟨1, by norm_num, fun p => p.elim⟩
    destination := Empty.elim
    hops := Empty.elim
    route := Empty.elim
    delivered := fun p => p.elim
    resource := fun p => p.elim
    causal := fun p => p.elim
    hop_sender := fun p => p.elim
    hop_receiver := fun p => p.elim
    load_le := fun r => Fin.elim0 r.1 }
  exact ⟨Empty, inferInstance, by simp, Empty.elim, fun v => v.elim, E,
    by simp [Execution.transportRate, E]⟩

theorem capacity_nonneg {n : ℕ} {R Δ W : ℝ}
    (hR : 0 ≤ R) (hΔ : 0 < Δ) (hW : 0 ≤ W) : 0 ≤ capacity n R Δ W :=
  (zero_achievable n R Δ W hW).le_capacity hR hΔ hW

theorem capacity_le {n : ℕ} {R Δ W : ℝ}
    (hR : 0 ≤ R) (hΔ : 0 < Δ) (hW : 0 ≤ W) :
    capacity n R Δ W ≤ W * upperConstant R Δ * Real.sqrt n :=
  csSup_le ⟨0, zero_achievable n R Δ W hW⟩ fun _ ht => achievable_le ht hR hΔ hW

theorem capacity_zero_bandwidth {n : ℕ} {R Δ : ℝ} (hR : 0 ≤ R) (hΔ : 0 < Δ) :
    capacity n R Δ 0 = 0 := by
  exact le_antisymm (by simpa using capacity_le (n := n) hR hΔ (le_refl 0))
    (capacity_nonneg hR hΔ (le_refl 0))

end

end CapacityAtlas.WirelessTransport
