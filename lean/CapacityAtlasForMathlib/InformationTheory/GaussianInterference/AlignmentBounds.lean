/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.AlignmentMeasure
import Mathlib.Analysis.SpecificLimits.Basic

open scoped BigOperators
open Filter Topology

namespace CapacityAtlas.Gaussian.Interference

variable {U : Type*} [Fintype U] [DecidableEq U] {n : ℕ}

omit [Fintype U] in
theorem beamExponent_le (a : Box U n) (p : U × U) : beamExponent a p ≤ n := by
  unfold beamExponent
  split_ifs with hp
  · exact (a ⟨p, hp⟩).isLt.le
  · exact Nat.zero_le _

def beamBound (U : Type*) [Fintype U] (n : ℕ) (M : ℝ) : ℝ :=
  (max 1 M) ^ (n * Fintype.card (U × U))

omit [DecidableEq U] in
theorem beamBound_pos (M : ℝ) : 0 < beamBound U n M := by
  unfold beamBound
  positivity

theorem norm_beam_le (h : U × U → ℂ) (M : ℝ) (hh : ∀ p, ‖h p‖ ≤ M)
    (a : Box U n) : ‖beam h a‖ ≤ beamBound U n M := by
  classical
  unfold beam beamBound
  rw [norm_prod]
  calc
    _ ≤ ∏ _ : U × U, (max 1 M) ^ n := by
      apply Finset.prod_le_prod
      · intro p _
        exact norm_nonneg _
      · intro p _
        rw [norm_pow]
        calc
          _ ≤ (max 1 M) ^ beamExponent a p := by
            gcongr
            exact (hh p).trans (le_max_right _ _)
          _ ≤ (max 1 M) ^ n := by
            exact pow_le_pow_right₀ (le_max_left _ _) (beamExponent_le a p)
    _ = (max 1 M) ^ (n * Fintype.card (U × U)) := by
      simp [← pow_mul]

theorem norm_transmitted_le (h : FadingBlock U n ℂ) (M Q : ℝ)
    (hh : ∀ r p, ‖h r p‖ ≤ M)
    (x : Box U n → ℂ) (hx : ∀ a, ‖x a‖ ≤ Q) (r : Columns U n) :
    ‖transmitted h x r‖ ≤ Fintype.card (Box U n) * beamBound U n M * Q := by
  classical
  calc
    _ ≤ ∑ a, ‖beam (h r) a * x a‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Box U n, beamBound U n M * Q := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_mul]
      exact mul_le_mul (norm_beam_le _ M (hh r) a) (hx a) (norm_nonneg _)
        (beamBound_pos M).le
    _ = _ := by simp [mul_assoc]

theorem monomial_fraction_tendsto (g : ℕ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ g / ((n : ℝ) ^ g + ((n : ℝ) + 1) ^ g))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have ht : Tendsto (fun n : ℕ ↦ ((n : ℝ) / ((n : ℝ) + 1)) ^ g) atTop (𝓝 1) := by
    simpa using (tendsto_natCast_div_add_atTop (1 : ℝ)).pow g
  have hf := ht.div (ht.add tendsto_const_nhds) (by norm_num : (1 : ℝ) + 1 ≠ 0)
  convert hf using 1
  · funext n
    have hp : 0 < ((n : ℝ) + 1) ^ g := by positivity
    have hs : 0 < (n : ℝ) ^ g + ((n : ℝ) + 1) ^ g := by positivity
    dsimp only [Pi.div_apply]
    rw [div_pow]
    field_simp
  · norm_num

theorem stream_fraction_tendsto :
    Tendsto (fun n : ℕ ↦ (Fintype.card (Box U n) : ℝ) / Fintype.card (Columns U n))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  simpa only [card_box, card_columns, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
    monomial_fraction_tendsto (Fintype.card (Cross U))

end CapacityAtlas.Gaussian.Interference
