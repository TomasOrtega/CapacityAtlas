/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

open scoped BigOperators

namespace CapacityAtlas.Multisource

noncomputable def roundedDemand (scale : ℕ) (margin rate : ℝ) : ℕ :=
  ⌊(scale : ℝ) * max (rate - margin) 0⌋₊

theorem sum_roundedDemand_le_cut {I E : Type*} [Fintype E]
    (inside : Finset I) (crossing : Finset E) (rate : I → ℝ) (capacity : E → ℝ)
    (hrate : ∀ i, 0 ≤ rate i)
    (hcut : ∑ i ∈ inside, rate i ≤ ∑ e ∈ crossing, capacity e)
    (scale : ℕ) (margin : ℝ) (hmargin : 0 ≤ margin)
    (hscale : (Fintype.card E : ℝ) ≤ scale * margin) :
    ∑ i ∈ inside, roundedDemand scale margin (rate i) ≤
      ∑ e ∈ crossing, ⌊(scale : ℝ) * capacity e⌋₊ := by
  classical
  by_cases hactive : ∃ i ∈ inside, margin < rate i
  · obtain ⟨i, hi, hirate⟩ := hactive
    have hsum : ∑ j ∈ inside, max (rate j - margin) 0 ≤
        (∑ j ∈ inside, rate j) - margin := by
      have hterm : ∀ j ∈ inside.erase i, max (rate j - margin) 0 ≤ rate j := by
        intro j _
        exact max_le (sub_le_self _ hmargin) (hrate j)
      have hh := Finset.sum_le_sum hterm
      rw [← Finset.sum_erase_add inside rate hi,
        ← Finset.sum_erase_add inside (fun j ↦ max (rate j - margin) 0) hi]
      rw [max_eq_left (sub_nonneg.mpr hirate.le)]
      linarith
    have hlower : (∑ e ∈ crossing, (⌊(scale : ℝ) * capacity e⌋₊ : ℝ)) ≥
        (scale : ℝ) * (∑ e ∈ crossing, capacity e) - crossing.card := by
      have h := Finset.sum_le_sum (s := crossing) (fun e _ ↦
        (Nat.lt_floor_add_one ((scale : ℝ) * capacity e)).le)
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
        ← Finset.mul_sum] at h
      linarith
    have hupper : (∑ j ∈ inside, (roundedDemand scale margin (rate j) : ℝ)) ≤
        (scale : ℝ) * ((∑ j ∈ inside, rate j) - margin) := by
      calc
        _ ≤ ∑ j ∈ inside, (scale : ℝ) * max (rate j - margin) 0 := by
          apply Finset.sum_le_sum
          intro j _
          exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _))
        _ = (scale : ℝ) * ∑ j ∈ inside, max (rate j - margin) 0 :=
          (Finset.mul_sum _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    have hcard : (crossing.card : ℝ) ≤ Fintype.card E := by
      exact_mod_cast Finset.card_le_univ crossing
    have hmul := mul_le_mul_of_nonneg_left hcut (Nat.cast_nonneg scale : (0 : ℝ) ≤ scale)
    have hresult : (∑ j ∈ inside, (roundedDemand scale margin (rate j) : ℝ)) ≤
        ∑ e ∈ crossing, (⌊(scale : ℝ) * capacity e⌋₊ : ℝ) := by
      nlinarith
    exact_mod_cast hresult
  · push Not at hactive
    have hzero : ∀ i ∈ inside, roundedDemand scale margin (rate i) = 0 := by
      intro i hi
      simp [roundedDemand, max_eq_right (sub_nonpos.mpr (hactive i hi))]
    simp [Finset.sum_eq_zero hzero]

theorem roundedDemand_rate_lower (scale : ℕ) (hscale : 0 < scale)
    (margin rate : ℝ) :
    rate - margin - (scale : ℝ)⁻¹ ≤
      (roundedDemand scale margin rate : ℝ) / scale := by
  have hpos : (0 : ℝ) < scale := by exact_mod_cast hscale
  have h := Nat.lt_floor_add_one ((scale : ℝ) * max (rate - margin) 0)
  have hm := le_max_left (rate - margin) 0
  apply (le_div_iff₀ hpos).mpr
  dsimp [roundedDemand]
  have hi : (scale : ℝ)⁻¹ * scale = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
  nlinarith [mul_le_mul_of_nonneg_left hm hpos.le]

end CapacityAtlas.Multisource
