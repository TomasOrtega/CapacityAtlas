/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.AlignmentChannel
import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.LogarithmicInterpolation
import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.ConverseAsymptotics

open Filter Topology

namespace CapacityAtlas.Gaussian.Interference

theorem alignment_slope_tendsto (K : ℕ) :
    Tendsto (fun n : ℕ ↦ (K : ℝ) * (1 - 1 / ((n : ℝ) + 1)) *
      ((Fintype.card (Box (Fin K) n) : ℝ) / extensionLength K n))
      atTop (𝓝 ((K : ℝ) / 2)) := by
  have hε : Tendsto (fun n : ℕ ↦ (1 : ℝ) - 1 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hr := stream_fraction_tendsto (U := Fin K)
  convert (hε.const_mul (K : ℝ)).mul hr using 1 <;> simp [extensionLength, div_eq_mul_inv]

/-- Matching alignment slopes and the Gaussian logarithmic upper bound determine the prelog. -/
theorem prelog_of_alignment_grid {K : ℕ} {F : ℝ → ℝ} (hF : Monotone F)
    {c : ℝ} (hc : 0 < c)
    (hupper : ∀ᶠ P : ℝ in atTop, F P ≤ (K : ℝ) / 2 * Real.log (1 + c * P))
    (hlower : ∀ n : ℕ, 0 < n → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∃ b : ℝ, ∀ᶠ q : ℕ in atTop,
        ((K : ℝ) * (1 - ε) * 2 * Fintype.card (Box (Fin K) n) /
          extensionLength K n) * Real.log q - b ≤ F (C * (q : ℝ) ^ 2)) :
    Tendsto (fun P : ℝ ↦ F P / Real.log P) atTop (𝓝 ((K : ℝ) / 2)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨d, had, hdk⟩ := exists_between ha
    have hs := (alignment_slope_tendsto K).eventually (isOpen_Ioi.mem_nhds hdk)
    obtain ⟨n, hn, hdn⟩ := ((eventually_ge_atTop (1 : ℕ)).and hs).exists
    have heps : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    obtain ⟨C, hC, b, hgrid⟩ := hlower n (by omega) _ heps
    have hd : d <
        ((K : ℝ) * (1 - 1 / ((n : ℝ) + 1)) * 2 * Fintype.card (Box (Fin K) n) /
          extensionLength K n) / 2 := by
      have heq :
          ((K : ℝ) * (1 - 1 / ((n : ℝ) + 1)) * 2 * Fintype.card (Box (Fin K) n) /
            extensionLength K n) / 2 =
          (K : ℝ) * (1 - 1 / ((n : ℝ) + 1)) *
            ((Fintype.card (Box (Fin K) n) : ℝ) / extensionLength K n) := by ring
      rw [heq]
      exact hdn
    filter_upwards [eventually_lower_bound_of_quadratic_grid hF hC hd hgrid] with P hP
    exact had.trans_le hP
  · intro b hb
    have hlim : Tendsto (fun P : ℝ ↦ (K : ℝ) / 2 *
        (Real.log (1 + c * P) / Real.log P)) atTop (𝓝 ((K : ℝ) / 2)) := by
      simpa using (log_affine_div_log_tendsto hc).const_mul ((K : ℝ) / 2)
    filter_upwards [hupper, hlim.eventually (isOpen_Iio.mem_nhds hb),
      eventually_gt_atTop (1 : ℝ)] with P hup hbP hP
    apply lt_of_le_of_lt _ hbP
    simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_right hup (Real.log_pos hP).le

end CapacityAtlas.Gaussian.Interference
