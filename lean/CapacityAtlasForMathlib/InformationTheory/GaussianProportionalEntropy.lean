/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open Real

namespace CapacityAtlas.MeasureInformation

/-- The proportional Gaussian reference maximizes the weighted logarithmic difference. -/
theorem weighted_log_sub_le_of_proportional
    {P Q A B f g : ℝ} (hP : 0 < P) (hQ : 0 < Q) (hA : 0 < A) (hB : 0 < B)
    (hAB : A ≤ B) (hPQ : P + (B - A) ≤ Q) (hg : 0 < g) (hf : f = g * A / B) :
    f * log P - g * log Q ≤ f * log A - g * log B := by
  let θ := A / B
  have hθ : 0 ≤ θ := (div_pos hA hB).le
  have hθ1 : θ ≤ 1 := (div_le_one hB).mpr hAB
  have hsum : θ + (1 - θ) = 1 := by ring
  have hj := strictConcaveOn_log_Ioi.concaveOn.2 (show P / A ∈ Set.Ioi (0 : ℝ) from div_pos hP hA)
    (by norm_num : (1 : ℝ) ∈ Set.Ioi (0 : ℝ)) hθ (sub_nonneg.mpr hθ1) hsum
  simp only [smul_eq_mul, log_one, mul_zero, add_zero, mul_one] at hj
  have hbase : 0 < θ * (P / A) + (1 - θ) := by
    exact add_pos_of_pos_of_nonneg (mul_pos (div_pos hA hB) (div_pos hP hA))
      (sub_nonneg.mpr hθ1)
  have hupper : θ * (P / A) + (1 - θ) ≤ Q / B := by
    dsimp [θ]
    field_simp
    nlinarith
  have hl := hj.trans (log_le_log hbase hupper)
  rw [log_div hP.ne' hA.ne', log_div hQ.ne' hB.ne'] at hl
  have hmul := mul_le_mul_of_nonneg_left hl hg.le
  rw [hf]
  dsimp [θ] at hmul
  simp only [div_eq_mul_inv] at hmul ⊢
  nlinarith

theorem proportional_log_sub_le
    {P Q A B a : ℝ} (hP : 0 < P) (hQ : 0 < Q) (hA : 0 < A) (hB : 0 < B)
    (ha1 : a ≤ 1) (hAeq : A = a * B) (hPQ : P + (B - A) ≤ Q) :
    a * log P - log Q ≤ a * log A - log B := by
  have hAB : A ≤ B := by rw [hAeq]; nlinarith
  have hf : a = (1 : ℝ) * A / B := by rw [one_mul, hAeq, mul_div_cancel_right₀ a hB.ne']
  simpa only [one_mul] using weighted_log_sub_le_of_proportional hP hQ hA hB hAB hPQ zero_lt_one hf

end CapacityAtlas.MeasureInformation
