/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Filter Topology

namespace CapacityAtlas.Gaussian.Interference

noncomputable def qamOrder (C P : ℝ) : ℕ := ⌊Real.sqrt (P / C)⌋₊

theorem qamOrder_tendsto {C : ℝ} (hC : 0 < C) :
    Tendsto (qamOrder C) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    (Real.tendsto_sqrt_atTop.comp (tendsto_id.atTop_div_const hC))

theorem qamOrder_power_le {C P : ℝ} (hC : 0 < C) (hP : 0 ≤ P) :
    C * (qamOrder C P : ℝ) ^ 2 ≤ P := by
  have hq : (qamOrder C P : ℝ) ≤ Real.sqrt (P / C) := Nat.floor_le (Real.sqrt_nonneg _)
  have hs := Real.sq_sqrt (div_nonneg hP hC.le)
  have hq0 : (0 : ℝ) ≤ qamOrder C P := Nat.cast_nonneg _
  have hp : (qamOrder C P : ℝ) ^ 2 ≤ P / C := by nlinarith [Real.sqrt_nonneg (P / C)]
  simpa only [mul_comm] using (le_div_iff₀ hC).mp hp

theorem log_qamOrder_div_log_tendsto {C : ℝ} (hC : 0 < C) :
    Tendsto (fun P : ℝ ↦ Real.log (qamOrder C P) / Real.log P) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hs : Tendsto (fun P : ℝ ↦ Real.sqrt (P / C)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_id.atTop_div_const hC)
  have hr : Tendsto (fun P : ℝ ↦ (qamOrder C P : ℝ) / Real.sqrt (P / C))
      atTop (𝓝 1) := tendsto_nat_floor_div_atTop.comp hs
  have hl : Tendsto (fun P : ℝ ↦ Real.log ((qamOrder C P : ℝ) / Real.sqrt (P / C)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hr
  have he := hl.div_atTop Real.tendsto_log_atTop
  have hc : Tendsto (fun P : ℝ ↦ Real.log C / Real.log P) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hf : Tendsto (fun P : ℝ ↦ (1 / 2 : ℝ) - (Real.log C / Real.log P) / 2 +
      Real.log ((qamOrder C P : ℝ) / Real.sqrt (P / C)) / Real.log P)
      atTop (𝓝 (1 / 2 : ℝ)) := by
    convert (tendsto_const_nhds.sub (hc.div_const 2)).add he using 1
    norm_num
  apply hf.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (qamOrder_tendsto hC).eventually_ge_atTop 1] with P hP hq
  have hPn : P ≠ 0 := by linarith
  have hq0 : (qamOrder C P : ℝ) ≠ 0 := by exact_mod_cast (by omega : qamOrder C P ≠ 0)
  have hs0 : Real.sqrt (P / C) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (div_pos (by linarith) hC))
  rw [Real.log_div hq0 hs0, Real.log_sqrt (div_nonneg (by linarith) hC.le),
    Real.log_div hPn hC.ne']
  have hlP : Real.log P ≠ 0 := ne_of_gt (Real.log_pos hP)
  field_simp
  ring

/-- A lower bound at quadratic powers extends to every sufficiently large power. -/
theorem eventually_lower_bound_of_quadratic_grid {F : ℝ → ℝ} (hF : Monotone F)
    {C a b d : ℝ} (hC : 0 < C) (hd : d < a / 2)
    (hb : ∀ᶠ q : ℕ in atTop, a * Real.log q - b ≤ F (C * (q : ℝ) ^ 2)) :
    ∀ᶠ P : ℝ in atTop, d ≤ F P / Real.log P := by
  have hlim : Tendsto
      (fun P : ℝ ↦ (a * Real.log (qamOrder C P) - b) / Real.log P)
      atTop (𝓝 (a / 2)) := by
    have h₁ := (log_qamOrder_div_log_tendsto hC).const_mul a
    have h₂ : Tendsto (fun P : ℝ ↦ b / Real.log P) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    convert h₁.sub h₂ using 1
    · funext P
      ring
    · simp [div_eq_mul_inv]
  filter_upwards [hlim.eventually (isOpen_Ioi.mem_nhds hd), (qamOrder_tendsto hC).eventually hb,
    eventually_gt_atTop (1 : ℝ)] with P hdP hbP hP
  apply hdP.le.trans
  apply div_le_div_of_nonneg_right _ (Real.log_pos hP).le
  exact hbP.trans (hF (qamOrder_power_le hC (by linarith)))

end CapacityAtlas.Gaussian.Interference
