/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteMeasureInformation
import CapacityAtlasForMathlib.InformationTheory.DifferentialEntropy
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal

namespace CapacityAtlas.MeasureInformation

variable {α β Ω : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace Ω]

/-- Testing one event in the Gibbs variational inequality. -/
theorem measure_mul_le_klDiv_add_log
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {s : Set α} (hs : MeasurableSet s) (c : ℝ) (hfinite : klDiv μ ν ≠ ⊤) :
    μ.real s * c ≤ (klDiv μ ν).toReal + log (1 + ν.real s * (exp c - 1)) := by
  classical
  let f : α → ℝ := s.indicator (fun _ ↦ c)
  have hf : Integrable f μ := (integrable_const c).indicator hs
  have hexp_eq : (fun x ↦ exp (f x)) =
      fun x ↦ 1 + s.indicator (fun _ ↦ exp c - 1) x := by
    funext x
    by_cases hx : x ∈ s <;> simp [f, hx]
  have hind : Integrable (s.indicator (fun _ ↦ exp c - 1)) ν :=
    (integrable_const _).indicator hs
  have hexp : Integrable (fun x ↦ exp (f x)) ν := by
    rw [hexp_eq]
    exact (integrable_const 1).add hind
  have hmean : (∫ x, f x ∂μ) = μ.real s * c := by
    simp [f, integral_indicator_const c hs, smul_eq_mul]
  have hpartition : (∫ x, exp (f x) ∂ν) = 1 + ν.real s * (exp c - 1) := by
    rw [hexp_eq, integral_add (integrable_const 1) hind]
    simp [integral_indicator_const _ hs, smul_eq_mul]
  have h := integral_sub_log_partition_le_klDiv hfinite hf hexp
  rw [hmean, hpartition] at h
  linarith

section FiniteMessages

variable [Fintype α] [MeasurableSingletonClass α]

theorem prod_measure_decoder_success (ρ : Measure (α × β)) [IsProbabilityMeasure ρ]
    {decode : β → α} (hdecode : Measurable decode)
    (huniform : ∀ m, ρ.fst {m} = (Fintype.card α : ℝ≥0∞)⁻¹) :
    (ρ.fst.prod ρ.snd).real {p | decode p.2 = p.1} = (Fintype.card α : ℝ)⁻¹ := by
  have hs : MeasurableSet {p : α × β | decode p.2 = p.1} :=
    measurableSet_eq_fun (hdecode.comp measurable_snd) measurable_fst
  have hmass : (ρ.fst.prod ρ.snd) {p | decode p.2 = p.1} =
      (Fintype.card α : ℝ≥0∞)⁻¹ := by
    rw [Measure.prod_apply_symm hs]
    have hsection (y : β) :
        (fun x : α ↦ (x, y)) ⁻¹' {p : α × β | decode p.2 = p.1} = {decode y} := by
      ext x
      simp [eq_comm]
    simp_rw [hsection, huniform]
    simp
  rw [Measure.real, hmass, ENNReal.toReal_inv]
  simp

/-- Joint decoding error under a specified message-observation law. -/
noncomputable def decodingError (ρ : Measure (α × β)) (decode : β → α) : ℝ :=
  ρ.real {p | decode p.2 ≠ p.1}

variable [Nonempty α]

/-- Fano's one-bit remainder for a uniform finite message and any measurable observation. -/
theorem fano_uniform_joint (ρ : Measure (α × β)) [IsProbabilityMeasure ρ]
    {decode : β → α} (hdecode : Measurable decode)
    (huniform : ∀ m, ρ.fst {m} = (Fintype.card α : ℝ≥0∞)⁻¹) :
    (1 - decodingError ρ decode) * log (Fintype.card α) ≤
      (mutualInfo ρ).toReal + log 2 := by
  have hs : MeasurableSet {p : α × β | decode p.2 = p.1} :=
    measurableSet_eq_fun (hdecode.comp measurable_snd) measurable_fst
  have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hcardone : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hinv : (Fintype.card α : ℝ)⁻¹ ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hcardone
  have h := measure_mul_le_klDiv_add_log ρ (ρ.fst.prod ρ.snd) hs
    (log (Fintype.card α)) (mutualInfo_ne_top_of_uniform ρ huniform)
  rw [prod_measure_decoder_success ρ hdecode huniform, exp_log hcard] at h
  have hpartition : 1 + (Fintype.card α : ℝ)⁻¹ * (Fintype.card α - 1) =
      2 - (Fintype.card α : ℝ)⁻¹ := by
    rw [mul_sub, inv_mul_cancel₀ hcard.ne', mul_one]
    ring
  have hpartition_pos : 0 < 2 - (Fintype.card α : ℝ)⁻¹ := by linarith
  have hlog : log (2 - (Fintype.card α : ℝ)⁻¹) ≤ log 2 :=
    log_le_log hpartition_pos (sub_le_self _ (inv_nonneg.mpr hcard.le))
  have hsuccess : ρ.real {p | decode p.2 = p.1} = 1 - decodingError ρ decode := by
    have hc := probReal_compl_eq_one_sub (μ := ρ) hs
    change decodingError ρ decode = 1 - ρ.real {p | decode p.2 = p.1} at hc
    linarith
  rw [hpartition, hsuccess] at h
  exact h.trans (by dsimp [mutualInfo]; linarith)

theorem fano_uniform_joint_log (ρ : Measure (α × β)) [IsProbabilityMeasure ρ]
    {decode : β → α} (hdecode : Measurable decode)
    (huniform : ∀ m, ρ.fst {m} = (Fintype.card α : ℝ≥0∞)⁻¹) :
    log (Fintype.card α) ≤ (mutualInfo ρ).toReal + log 2 +
      decodingError ρ decode * log (Fintype.card α) := by
  have h := fano_uniform_joint ρ hdecode huniform
  nlinarith

/-- Fano's bound in the nonnegative extended reals. -/
theorem fano_uniform_joint_ennreal (ρ : Measure (α × β)) [IsProbabilityMeasure ρ]
    {decode : β → α} (hdecode : Measurable decode)
    (huniform : ∀ m, ρ.fst {m} = (Fintype.card α : ℝ≥0∞)⁻¹) :
    ENNReal.ofReal ((1 - decodingError ρ decode) * log (Fintype.card α) - log 2) ≤
      mutualInfo ρ := by
  rw [ENNReal.ofReal_le_iff_le_toReal (mutualInfo_ne_top_of_uniform ρ huniform)]
  have h := fano_uniform_joint ρ hdecode huniform
  linarith

theorem fano_uniform (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → α} {Y : Ω → β} {decode : β → α}
    (hX : Measurable X) (hY : Measurable Y) (hdecode : Measurable decode)
    (huniform : ∀ m, (μ.map X) {m} = (Fintype.card α : ℝ≥0∞)⁻¹) :
    log (Fintype.card α) ≤ (mutualInfoRV X Y μ).toReal + log 2 +
      μ.real {ω | decode (Y ω) ≠ X ω} * log (Fintype.card α) := by
  let ρ := μ.map (fun ω ↦ (X ω, Y ω))
  letI : IsProbabilityMeasure ρ :=
    Measure.isProbabilityMeasure_map (hX.prodMk hY).aemeasurable
  have hprior (m : α) : ρ.fst {m} = (Fintype.card α : ℝ≥0∞)⁻¹ := by
    rw [Measure.fst_map_prodMk hY]
    exact huniform m
  have h := fano_uniform_joint_log ρ hdecode hprior
  have herror : decodingError ρ decode = μ.real {ω | decode (Y ω) ≠ X ω} := by
    have hs : MeasurableSet {p : α × β | decode p.2 ≠ p.1} :=
      (measurableSet_eq_fun (hdecode.comp measurable_snd) measurable_fst).compl
    rw [decodingError, Measure.real, Measure.map_apply (hX.prodMk hY) hs]
    rfl
  rw [herror] at h
  exact h

theorem fano_uniform_ennreal (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → α} {Y : Ω → β} {decode : β → α}
    (hX : Measurable X) (hY : Measurable Y) (hdecode : Measurable decode)
    (huniform : ∀ m, (μ.map X) {m} = (Fintype.card α : ℝ≥0∞)⁻¹) :
    ENNReal.ofReal ((1 - μ.real {ω | decode (Y ω) ≠ X ω}) *
      log (Fintype.card α) - log 2) ≤ mutualInfoRV X Y μ := by
  rw [ENNReal.ofReal_le_iff_le_toReal (mutualInfoRV_ne_top_of_uniform μ hX hY huniform)]
  have h := fano_uniform μ hX hY hdecode huniform
  nlinarith

end FiniteMessages

end CapacityAtlas.MeasureInformation
