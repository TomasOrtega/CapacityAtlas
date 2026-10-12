/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Network.Multisource.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace CapacityAtlas.Multisource.Network

variable {vertices edges sources : ℕ} {G : Network vertices edges sources}

namespace Code

variable {n : ℕ} (c : G.Code n)

noncomputable def parallel {N : ℕ} (copies : ℕ) (counts : Fin sources → ℕ)
    (hcounts : ∀ i, 0 < counts i)
    (messageEquiv : ∀ i, Fin (counts i) ≃ (Fin copies → Fin (c.messages i)))
    (packetMap : ∀ e, (Fin copies → G.Packet n e) ↪ G.Packet N e) : G.Code N where
  messages := counts
  messages_pos := hcounts
  packet m e := packetMap e (fun j ↦ c.packet (fun i ↦ messageEquiv i (m i) j) e)
  packet_local e m m' hm hp := by
    congr 1
    funext j
    apply c.packet_local
    · intro i hi
      rw [hm i hi]
    · intro a ha
      exact congrFun ((packetMap a).injective (hp a ha)) j
  decode v hv m i := (messageEquiv i).symm
    (fun j ↦ c.decode v hv (fun k ↦ messageEquiv k (m k) j) i)
  decode_local v hv m m' hm hp := by
    funext i
    congr 1
    funext j
    apply congrFun (c.decode_local v hv _ _ ?_ ?_) i
    · intro k hk
      rw [hm k hk]
    · intro a ha
      exact congrFun ((packetMap a).injective (hp a ha)) j

theorem parallel_perfect {N : ℕ} (copies : ℕ) (counts : Fin sources → ℕ)
    (hcounts : ∀ i, 0 < counts i)
    (messageEquiv : ∀ i, Fin (counts i) ≃ (Fin copies → Fin (c.messages i)))
    (packetMap : ∀ e, (Fin copies → G.Packet n e) ↪ G.Packet N e)
    (hc : ∀ m, c.Successful m) :
    ∀ m, (c.parallel copies counts hcounts messageEquiv packetMap).Successful m := by
  intro m v hv
  funext i
  apply (messageEquiv i).injective
  funext j
  simp only [parallel, Equiv.apply_symm_apply]
  exact congrFun (hc _ v hv) i

theorem error_eq_zero_of_perfect (hc : ∀ m, c.Successful m) : c.error = 0 := by
  classical
  have hcount : c.successCount = Fintype.card (Message c.messages) := by
    unfold successCount
    simp [hc]
  have hpos : Fintype.card (Message c.messages) ≠ 0 := Fintype.card_ne_zero
  unfold error
  rw [hcount, div_self (Nat.cast_ne_zero.mpr hpos), sub_self]

end Code

theorem packetBits_copies_le {n N : ℕ} (copies : ℕ) (h : copies * n ≤ N)
    (e : Fin edges) : copies * G.packetBits n e ≤ G.packetBits N e := by
  apply Nat.le_floor
  push_cast
  have hfloor := Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) (G.linkRate_nonneg e))
  have hcast : (copies : ℝ) * n ≤ N := by exact_mod_cast h
  have hmul := mul_le_mul_of_nonneg_right hcast (G.linkRate_nonneg e)
  dsimp [packetBits] at *
  nlinarith [mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg copies : (0 : ℝ) ≤ copies)]

namespace Code

variable {n : ℕ} (c : G.Code n)

noncomputable def replicate {N : ℕ} (copies : ℕ) (h : copies * n ≤ N) : G.Code N :=
  c.parallel copies (fun i ↦ c.messages i ^ copies)
    (fun i ↦ pow_pos (c.messages_pos i) _)
    (fun i ↦ Fintype.equivOfCardEq (by simp))
    (fun e ↦ Classical.choice (Function.Embedding.nonempty_of_card_le (by
      simp only [Fintype.card_fun, Fintype.card_fin]
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by
        simpa [Nat.mul_comm] using packetBits_copies_le copies h e))))

theorem repeat_messages {N : ℕ} (copies : ℕ) (h : copies * n ≤ N) (i : Fin sources) :
    (c.replicate copies h).messages i = c.messages i ^ copies := rfl

theorem repeat_perfect {N : ℕ} (copies : ℕ) (h : copies * n ≤ N)
    (hc : ∀ m, c.Successful m) : ∀ m, (c.replicate copies h).Successful m :=
  c.parallel_perfect _ _ _ _ _ hc

theorem repeat_rate {N : ℕ} (copies : ℕ) (h : copies * n ≤ N) (i : Fin sources) :
    (c.replicate copies h).rate i =
      (copies : ℝ) * Real.logb 2 (c.messages i) / N := by
  simp [rate, Operational.messageRate, repeat_messages, Nat.cast_pow, Real.logb_pow]

theorem log_messages_nonneg (i : Fin sources) : 0 ≤ Real.logb 2 (c.messages i) := by
  apply Real.logb_nonneg (by norm_num)
  exact_mod_cast c.messages_pos i

theorem rate_achievable_of_perfect (hn : 0 < n) (hc : ∀ m, c.Successful m) :
    c.rate ∈ G.capacityRegion := by
  classical
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog := c.log_messages_nonneg
  refine ⟨fun i ↦ div_nonneg (hlog i) hnreal.le, fun ε hε ↦ ?_⟩
  let total : ℝ := ∑ i, Real.logb 2 (c.messages i)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (total / ε) 0)
  have hNpos : 0 < N := by exact_mod_cast (lt_of_le_of_lt (le_max_right _ _) hN)
  refine ⟨N, hNpos, fun m hm ↦ ?_⟩
  have hmpos : 0 < m := hNpos.trans_le hm
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hmpos
  let q := m / n
  have hqn : q * n ≤ m := Nat.div_mul_le_self m n
  let code := c.replicate q hqn
  refine ⟨code, trivial, (code.error_eq_zero_of_perfect (c.repeat_perfect q hqn hc)).le.trans hε.le,
    fun i ↦ ?_⟩
  have hlogtotal : Real.logb 2 (c.messages i) ≤ total :=
    Finset.single_le_sum (fun j _ ↦ hlog j) (Finset.mem_univ i)
  have htotal : total ≤ ε * m := by
    have hh : total / ε < (m : ℝ) :=
      (lt_of_le_of_lt (le_max_left _ _) hN).trans_le (by exact_mod_cast hm)
    simpa [mul_comm] using ((div_lt_iff₀ hε).mp hh).le
  have hq : (m : ℝ) ≤ (q : ℝ) * n + n := by
    have hh := (Nat.lt_mul_div_succ m hn).le
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm n (m / n)] at hh
    exact_mod_cast hh
  have hr : 0 ≤ c.rate i := div_nonneg (hlog i) hnreal.le
  have hrate : c.rate i * n = Real.logb 2 (c.messages i) := by
    exact div_mul_cancel₀ _ (ne_of_gt hnreal)
  have hqr := mul_le_mul_of_nonneg_right hq hr
  change c.rate i - ε ≤ (c.replicate q hqn).rate i
  rw [repeat_rate]
  apply (le_div_iff₀ hmreal).mpr
  nlinarith

end Code

theorem mem_capacityRegion_of_perfect_approximation (r : Fin sources → ℝ)
    (hr : ∀ i, 0 ≤ r i)
    (hcodes : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 0 < n ∧ ∃ c : G.Code n,
      (∀ m, c.Successful m) ∧ ∀ i, r i - ε ≤ c.rate i) :
    r ∈ G.capacityRegion := by
  refine ⟨hr, fun ε hε ↦ ?_⟩
  obtain ⟨n, hn, c, hc, hrate⟩ := hcodes (ε / 2) (half_pos hε)
  obtain ⟨N, hN, hNcodes⟩ := (c.rate_achievable_of_perfect hn hc).2 (ε / 2) (half_pos hε)
  refine ⟨N, hN, fun m hm ↦ ?_⟩
  obtain ⟨code, hadmissible, herror, hrates⟩ := hNcodes m hm
  refine ⟨code, hadmissible, herror.trans (by linarith), fun i ↦ ?_⟩
  linarith [hrate i, hrates i]

end CapacityAtlas.Multisource.Network
