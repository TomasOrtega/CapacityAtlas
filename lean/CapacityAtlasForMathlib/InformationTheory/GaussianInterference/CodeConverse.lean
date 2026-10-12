/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.ConverseEnergy

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal

namespace CapacityAtlas.Gaussian.Interference

noncomputable def converseNoise (L U : ℝ) : ℝ := L ^ 2 / (2 * (L ^ 2 + U ^ 2))

theorem converseNoise_pos {L U : ℝ} (hL : 0 < L) : 0 < converseNoise L U := by
  unfold converseNoise
  positivity

theorem converseNoise_le_half {L U : ℝ} (hL : 0 < L) : converseNoise L U ≤ 1 / 2 := by
  unfold converseNoise
  rw [div_le_iff₀ (by positivity : 0 < 2 * (L ^ 2 + U ^ 2))]
  nlinarith [sq_nonneg U]

theorem converseNoise_ratio_bound {L U : ℝ} (hL : 0 < L) (hU : 0 ≤ U)
    {a b : ℂ} (ha : ‖a‖ ≤ U) (hb : L ≤ ‖b‖) :
    converseNoise L U * ‖a / b‖ ^ 2 ≤ 1 / 2 := by
  have hbpos : 0 < ‖b‖ := hL.trans_le hb
  have hr : ‖a / b‖ ≤ U / L := by
    rw [norm_div, div_le_div_iff₀ hbpos hL]
    nlinarith
  have hs : ‖a / b‖ ^ 2 ≤ (U / L) ^ 2 := by gcongr
  have hh : converseNoise L U * (U / L) ^ 2 ≤ 1 / 2 := by
    unfold converseNoise
    rw [div_pow]
    have hsq : L ^ 2 ≠ 0 := pow_ne_zero _ hL.ne'
    have heq : L ^ 2 / (2 * (L ^ 2 + U ^ 2)) * (U ^ 2 / L ^ 2) =
        U ^ 2 / (2 * (L ^ 2 + U ^ 2)) := by field_simp
    rw [heq, div_le_iff₀ (by positivity : 0 < 2 * (L ^ 2 + U ^ 2))]
    nlinarith [sq_nonneg L]
  exact (mul_le_mul_of_nonneg_left hs (converseNoise_pos hL).le).trans hh

theorem stateLaw_ae_annulus (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {L U : ℝ} (hμ : ∀ᵐ z ∂μ, L ≤ ‖z‖ ∧ ‖z‖ ≤ U) (K n : ℕ) :
    ∀ᵐ H ∂stateLaw μ K n, ∀ t i j, L ≤ ‖H t i j‖ ∧ ‖H t i j‖ ≤ U := by
  apply ae_all_iff.mpr
  intro t
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  have hrow := (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin K ↦ μ) (i := j)).eventually hμ
  have hmatrix := (Measure.tendsto_eval_ae_ae
    (μ := fun _ : Fin K ↦ Measure.pi fun _ : Fin K ↦ μ) (i := i)).eventually hrow
  exact (Measure.tendsto_eval_ae_ae
    (μ := fun _ : Fin n ↦ Measure.pi fun _ : Fin K ↦ Measure.pi fun _ : Fin K ↦ μ)
    (i := t)).eventually hmatrix

theorem code_pair_converse (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {L U P : ℝ} (hL : 0 < L) (hU : 0 ≤ U) (hP : 0 ≤ P)
    (hμ : ∀ᵐ z ∂μ, L ≤ ‖z‖ ∧ ‖z‖ ≤ U)
    {K n : ℕ} (c : Code K n) (hc : PowerAdmissible μ P c)
    (i j : Fin K) (hij : i ≠ j) :
    (1 - error μ c) * (Real.log (c.messages i) + Real.log (c.messages j)) ≤
      (n : ℝ) * Real.log (1 + U ^ 2 * P / converseNoise L U) + 2 * Real.log 2 := by
  let e := converseNoise L U
  let t := e + U ^ 2 * P
  have he : 0 < e := converseNoise_pos hL
  have ht : 0 < t := by dsimp [t]; positivity
  have hstate := stateLaw_ae_annulus μ hμ K n
  have hupper : ∀ᵐ H ∂stateLaw μ K n,
      (∀ s, ‖H s i i‖ ≤ U) ∧ (∀ s, ‖H s i j‖ ≤ U) := by
    filter_upwards [hstate] with H hh
    exact ⟨fun s ↦ (hh s i i).2, fun s ↦ (hh s i j).2⟩
  have hienergy := integrable_messageAverage μ c (fun m H ↦ pairEnergy c H i j m)
    (integrable_pairEnergy μ c hc hU i j hij hupper)
  have hierror (k : Fin K) := integrable_messageAverage μ c
    (fun m H ↦ receiverErrorAt c m H k) (fun m ↦ integrable_receiverErrorAt μ c m k)
  have herror (k : Fin K) :
      (∫ H, ∫ m, receiverErrorAt c m H k ∂messageLaw c ∂stateLaw μ K n) ≤ error μ c := by
    rw [integral_state_messageAverage μ c _ (fun m ↦ integrable_receiverErrorAt μ c m k)]
    exact average_receiverErrorAt_le_error μ c k
  have henergy : (∫ H, ∫ m, pairEnergy c H i j m ∂messageLaw c ∂stateLaw μ K n) ≤
      2 * n * (t - e) := by
    convert integral_pairEnergy_le μ c hc hU i j hij hupper using 1
    dsimp [t]
    ring
  have hpointwise : ∀ᵐ H ∂stateLaw μ K n,
      Real.log (c.messages i) + Real.log (c.messages j) ≤
        (n : ℝ) * Real.log (t / e) +
        ((2 * n : ℝ) * e + (∫ m, pairEnergy c H i j m ∂messageLaw c)) / (2 * t) -
          n + 2 * Real.log 2 +
        (∫ m, receiverErrorAt c m H i ∂messageLaw c) * Real.log (c.messages i) +
        (∫ m, receiverErrorAt c m H j ∂messageLaw c) * Real.log (c.messages j) := by
    filter_upwards [hstate] with H hh
    apply code_pair_fano_at_state c H i j hij
      (fun s ↦ norm_pos_iff.mp (hL.trans_le (hh s i j).1)) he ht (converseNoise_le_half hL)
    intro s
    exact converseNoise_ratio_bound hL hU (hh s j j).2 (hh s i j).1
  have hlog (k : Fin K) : 0 ≤ Real.log (c.messages k) :=
    Real.log_nonneg (by exact_mod_cast c.messages_pos k)
  have hf := pair_bound_of_integrated_energy (stateLaw μ K n) ht (hlog i) (hlog j)
    hienergy (hierror i) (hierror j) henergy (herror i) (herror j) hpointwise
  have heq : t / e = 1 + U ^ 2 * P / e := by dsimp [t]; field_simp
  rw [heq] at hf
  exact hf

end CapacityAtlas.Gaussian.Interference
