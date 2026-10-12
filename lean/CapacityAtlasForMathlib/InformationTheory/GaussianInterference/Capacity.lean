/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.Achievability
import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.CapacityConverse
import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.AsymptoticSqueeze

open MeasureTheory Filter
open scoped Topology

namespace CapacityAtlas.Gaussian.Interference

/-- The fully connected time-varying interference channel has K/2 sum degrees of freedom. -/
theorem sum_degrees_of_freedom (μ : Measure ℂ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {K : ℕ} (hK : 2 ≤ K) {L U : ℝ} (hL : 0 < L) (hU : 0 ≤ U)
    (hμ : ∀ᵐ z ∂μ, L ≤ ‖z‖ ∧ ‖z‖ ≤ U) :
    Tendsto (fun P : ℝ ↦ sumCapacity μ K P / Real.logb 2 P)
      atTop (𝓝 ((K : ℝ) / 2)) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hUp : 0 < U := annulus_upper_pos μ hL hμ
  let F : ℝ → ℝ := fun P ↦ sumCapacity μ K P * Real.log 2
  have hmono : Monotone F := fun P P' h ↦
    mul_le_mul_of_nonneg_right (sumCapacity_monotone μ hL hU hμ hK h) hlog.le
  have hc : 0 < U ^ 2 / converseNoise L U := by
    exact div_pos (sq_pos_of_pos hUp) (converseNoise_pos hL)
  have hupper : ∀ᶠ P : ℝ in atTop,
      F P ≤ (K : ℝ) / 2 * Real.log (1 + (U ^ 2 / converseNoise L U) * P) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with P hP
    have hp := mul_le_mul_of_nonneg_right (sumCapacity_converse μ hL hU hP hμ hK) hlog.le
    change F P ≤ _ at hp
    convert hp using 1
    rw [Real.logb]
    have he : 1 + U ^ 2 * P / converseNoise L U =
        1 + (U ^ 2 / converseNoise L U) * P := by ring
    rw [he]
    field_simp
  have hlower : ∀ n : ℕ, 0 < n → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∃ b : ℝ, ∀ᶠ q : ℕ in atTop,
        ((K : ℝ) * (1 - ε) * 2 * Fintype.card (Box (Fin K) n) /
          extensionLength K n) * Real.log q - b ≤ F (C * (q : ℝ) ^ 2) := by
    intro n hn ε hε
    exact exists_quadratic_grid_lower μ (by omega) U
      (hμ.mono fun _ h ↦ h.2) (sumRates_bddAbove_all μ hL hU hμ hK) hn hε
  have hpre := prelog_of_alignment_grid hmono hc hupper hlower
  convert hpre using 1
  funext P
  simp only [Real.logb, F, div_div_eq_mul_div]

end CapacityAtlas.Gaussian.Interference
