/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

open scoped BigOperators
open Filter Topology

namespace CapacityAtlas.Gaussian.Interference

theorem sum_le_of_pair_bounds {K : ℕ} (hK : 2 ≤ K) (R : Fin K → ℝ) (B : ℝ)
    (h : ∀ i j, i ≠ j → R i + R j ≤ B) : ∑ i, R i ≤ (K : ℝ) / 2 * B := by
  have hp : ∑ i, ∑ j, (R i + R j) ≤
      ∑ i, ∑ j, (if i = j then 2 * R i else B) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    split_ifs with hij
    · subst j
      linarith
    · exact h i j hij
  have hrow (i : Fin K) :
      (∑ j, if i = j then 2 * R i else B) = (K : ℝ) * B + (2 * R i - B) := by
    calc
      _ = ∑ j, (B + if i = j then 2 * R i - B else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> ring
      _ = _ := by simp [Finset.sum_add_distrib]
  simp only [hrow, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at hp
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hm : 0 < (K : ℝ) - 1 := by linarith
  have hh : ((K : ℝ) - 1) * (2 * (∑ i, R i) - K * B) ≤ 0 := by nlinarith [hp]
  have hz : 2 * (∑ i, R i) - K * B ≤ 0 :=
    le_of_not_gt (fun hz ↦ not_le_of_gt (mul_pos hm hz) hh)
  nlinarith

theorem log_affine_div_log_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun P : ℝ ↦ Real.log (1 + a * P) / Real.log P) atTop (𝓝 1) := by
  have ht : Tendsto (fun P : ℝ ↦ a + 1 / P) atTop (𝓝 a) := by
    have h : Tendsto (fun P : ℝ ↦ 1 / P) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa using tendsto_const_nhds.add h
  have hl : Tendsto (fun P : ℝ ↦ Real.log (a + 1 / P)) atTop (𝓝 (Real.log a)) := by
    simpa only [Function.comp_def] using (Real.continuousAt_log ha.ne').tendsto.comp ht
  have he := hl.div_atTop Real.tendsto_log_atTop
  have hf : Tendsto (fun P : ℝ ↦ 1 + Real.log (a + 1 / P) / Real.log P)
      atTop (𝓝 1) := by simpa using tendsto_const_nhds.add he
  apply hf.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
  have hp : 0 < P := by linarith
  have hn : 0 < a + 1 / P := by positivity
  have heq : 1 + a * P = (a + 1 / P) * P := by field_simp; ring
  rw [heq, Real.log_mul hn.ne' hp.ne']
  field_simp [ne_of_gt (Real.log_pos hP)]
  ring

theorem logb_affine_div_logb_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun P : ℝ ↦ Real.logb 2 (1 + a * P) / Real.logb 2 P) atTop (𝓝 1) := by
  convert log_affine_div_log_tendsto ha using 1
  funext P
  simp only [Real.logb]
  by_cases hp : Real.log P = 0
  · simp [hp]
  · field_simp [hp, ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]

end CapacityAtlas.Gaussian.Interference
