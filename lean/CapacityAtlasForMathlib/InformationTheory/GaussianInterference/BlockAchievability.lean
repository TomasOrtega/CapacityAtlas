/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.BlockCoding
import Mathlib.Algebra.Order.Floor.Semifield

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

namespace CapacityAtlas.Gaussian.Interference.BlockScheme

private theorem tendsto_block_fraction (L : ℕ) :
    Tendsto (fun n : ℕ => ((n / L : ℕ) : ℝ) / n) atTop (𝓝 ((L : ℝ)⁻¹)) := by
  have h := (tendsto_nat_floor_mul_div_atTop (R := ℝ)
    (a := (L : ℝ)⁻¹) (by positivity)).comp tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, mul_comm (L : ℝ)⁻¹, ← div_eq_mul_inv,
    Nat.floor_div_eq_div] using h

variable {μ : Measure ℂ} [IsProbabilityMeasure μ] {K L : ℕ} {P : ℝ} {A : Type*}
variable [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A]
variable (S : BlockScheme μ K L P A)

/-- Independent finite outer codes preserve the physical model, including every large blocklength. -/
theorem capacityRegion_of_lt (hL : 0 < L) (hP : 0 ≤ P) (R : Fin K → ℝ)
    (hR : ∀ i, 0 ≤ R i)
    (hcap : ∀ i, R i < (S.channel i).informationCapacityBits / L) :
    R ∈ capacityRegion μ K P := by
  classical
  refine ⟨hR, fun ε hε => ?_⟩
  let η := ε / (K + 1 : ℕ)
  have hη : 0 < η := div_pos hε (by positivity)
  have hcodes : ∀ i : Fin K, ∃ N : ℕ, 0 < N ∧ ∀ b, N ≤ b →
      ∃ c : FiniteChannel.BlockCode (S.channel i) b,
        c.averageErrorProbability ≤ η ∧ (L : ℝ) * R i ≤ c.rate := by
    intro i
    apply (S.channel i).achievableRate_of_lt_informationCapacityBits
      (rate := (L : ℝ) * R i)
    · have h := (lt_div_iff₀ (by exact_mod_cast hL : 0 < (L : ℝ))).mp (hcap i)
      simpa only [mul_comm] using h
    · exact hη
  choose N hN hc using hcodes
  have hlengths : ∀ᶠ n : ℕ in atTop, ∀ i, N i ≤ n / L := by
    apply eventually_all.mpr
    intro i
    exact (Nat.tendsto_div_const_atTop hL.ne').eventually (eventually_ge_atTop (N i))
  have hrates : ∀ᶠ n : ℕ in atTop, ∀ i,
      R i - ε ≤ ((n / L : ℕ) : ℝ) / n * ((L : ℝ) * R i) := by
    apply eventually_all.mpr
    intro i
    have ht := (tendsto_block_fraction L).mul_const ((L : ℝ) * R i)
    have he : (L : ℝ)⁻¹ * ((L : ℝ) * R i) = R i := by
      rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hL.ne'), one_mul]
    rw [he] at ht
    exact (ht.eventually (eventually_gt_nhds (by linarith : R i - ε < R i))).mono
      fun _ hn => hn.le
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < n / L :=
    (Nat.tendsto_div_const_atTop hL.ne').eventually (eventually_gt_atTop 0)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hlengths.and (hrates.and hpos))
  refine ⟨max N₀ 1, by omega, fun n hn => ?_⟩
  obtain ⟨hncodes, hnrates, hnpos⟩ := hN₀ n (le_trans (le_max_left _ _) hn)
  choose c he hr using fun i => hc i (n / L) (hncodes i)
  let hpad : n / L * L ≤ n := Nat.div_mul_le_self n L
  refine ⟨S.concat hpad c, S.concat_powerAdmissible hpad hP c, ?_, fun i => ?_⟩
  · calc
      error μ (S.concat hpad c) ≤ ∑ i, (c i).averageErrorProbability :=
        S.concat_error_le hpad c
      _ ≤ ∑ _ : Fin K, η := Finset.sum_le_sum fun i _ => he i
      _ ≤ ε := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        dsimp [η]
        rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < ((K + 1 : ℕ) : ℝ))]
        norm_num only [Nat.cast_add, Nat.cast_one]
        nlinarith
  · change R i - ε ≤ rates (S.concat hpad c) i
    rw [S.concat_rates hpad hnpos c i]
    exact (hnrates i).trans (mul_le_mul_of_nonneg_left (hr i) (by positivity))

end CapacityAtlas.Gaussian.Interference.BlockScheme
