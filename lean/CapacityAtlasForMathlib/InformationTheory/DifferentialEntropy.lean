/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.InformationTheory.KullbackLeibler.Basic

open MeasureTheory Real
open scoped NNReal

namespace CapacityAtlas.MeasureInformation

variable {α : Type*} {mα : MeasurableSpace α}

/-- Entropy in nats relative to a reference measure; comparisons require integrable log density. -/
noncomputable def entropyWith (μ reference : Measure α) : ℝ :=
  -∫ x, llr μ reference x ∂μ

theorem llr_map_embedding {β : Type*} [MeasurableSpace β]
    (μ reference : Measure α) [SigmaFinite μ] [SigmaFinite reference]
    (hac : μ ≪ reference) {f : α → β} (hf : MeasurableEmbedding f) :
    (fun x ↦ llr (μ.map f) (reference.map f) (f x)) =ᵐ[μ] llr μ reference := by
  filter_upwards [hac.ae_le (hf.rnDeriv_map μ reference)] with x hx
  simp only [llr, hx]

theorem entropyWith_map_embedding {β : Type*} [MeasurableSpace β]
    (μ reference : Measure α) [SigmaFinite μ] [SigmaFinite reference]
    (hac : μ ≪ reference) {f : α → β} (hf : MeasurableEmbedding f) :
    entropyWith (μ.map f) (reference.map f) = entropyWith μ reference := by
  unfold entropyWith
  rw [hf.integral_map, integral_congr_ae (llr_map_embedding μ reference hac hf)]

theorem integrable_llr_map_embedding_iff {β : Type*} [MeasurableSpace β]
    (μ reference : Measure α) [SigmaFinite μ] [SigmaFinite reference]
    (hac : μ ≪ reference) {f : α → β} (hf : MeasurableEmbedding f) :
    Integrable (llr (μ.map f) (reference.map f)) (μ.map f) ↔
      Integrable (llr μ reference) μ := by
  rw [hf.integrable_map_iff]
  exact integrable_congr (llr_map_embedding μ reference hac hf)

theorem entropyWith_smul_reference {μ reference : Measure α} [IsProbabilityMeasure μ]
    [SigmaFinite reference] (hac : μ ≪ reference) (hlog : Integrable (llr μ reference) μ)
    (c : ℝ≥0) (hc : c ≠ 0) :
    entropyWith μ (c • reference) = entropyWith μ reference + log c := by
  unfold entropyWith
  rw [integral_congr_ae (llr_smul_nnreal_right hac c hc),
    integral_sub hlog (integrable_const _)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

theorem entropyWith_map_of_map_reference_eq_smul {β : Type*} [MeasurableSpace β]
    {μ reference : Measure α} {targetReference : Measure β}
    [IsProbabilityMeasure μ] [SigmaFinite reference] [SigmaFinite targetReference]
    (hac : μ ≪ reference) (hlog : Integrable (llr μ reference) μ)
    {f : α → β} (hf : MeasurableEmbedding f) (c : ℝ≥0) (hc : c ≠ 0)
    (hmap : reference.map f = c • targetReference) :
    entropyWith (μ.map f) targetReference = entropyWith μ reference - log c := by
  letI := μ.isProbabilityMeasure_map hf.measurable.aemeasurable
  have hac' : μ.map f ≪ targetReference := by
    have h := hf.absolutelyContinuous_map hac
    rw [hmap] at h
    exact h.trans (by exact Measure.smul_absolutelyContinuous)
  have hscaled := (integrable_llr_map_embedding_iff μ reference hac hf).mpr hlog
  rw [hmap] at hscaled
  have htarget : Integrable (llr (μ.map f) targetReference) (μ.map f) := by
    apply (hscaled.add (integrable_const (log c))).congr
    filter_upwards [llr_smul_nnreal_right hac' c hc] with x hx
    change llr (μ.map f) (c • targetReference) x + log c = _
    linarith
  have h := entropyWith_map_embedding μ reference hac hf
  rw [hmap, entropyWith_smul_reference hac' htarget c hc] at h
  linarith

theorem llr_tilted_self {reference : Measure α} [SigmaFinite reference] {f : α → ℝ}
    (hexp : Integrable (fun x ↦ exp (f x)) reference) :
    llr (reference.tilted f) reference =ᵐ[reference]
      fun x ↦ f x - log (∫ x, exp (f x) ∂reference) := by
  have hf : AEMeasurable f reference := by
    simpa using hexp.aemeasurable.log
  filter_upwards [llr_tilted_left Measure.AbsolutelyContinuous.rfl hexp hf,
    llr_self reference] with x hx hself
  simpa [hself] using hx

theorem integrable_llr_tilted_self {reference : Measure α} [SigmaFinite reference]
    {f : α → ℝ} (hexp : Integrable (fun x ↦ exp (f x)) reference)
    (hf : Integrable f (reference.tilted f)) :
    Integrable (llr (reference.tilted f) reference) (reference.tilted f) := by
  apply (hf.sub (integrable_const (log (∫ x, exp (f x) ∂reference)))).congr
  filter_upwards [(tilted_absolutelyContinuous reference f).ae_le (llr_tilted_self hexp)]
    with x hx using hx.symm

theorem entropyWith_tilted {reference : Measure α} [SigmaFinite reference] [NeZero reference]
    {f : α → ℝ} (hexp : Integrable (fun x ↦ exp (f x)) reference)
    (hf : Integrable f (reference.tilted f)) :
    entropyWith (reference.tilted f) reference =
      log (∫ x, exp (f x) ∂reference) - ∫ x, f x ∂(reference.tilted f) := by
  letI := isProbabilityMeasure_tilted hexp
  unfold entropyWith
  rw [integral_congr_ae
    ((tilted_absolutelyContinuous reference f).ae_le (llr_tilted_self hexp)),
    integral_sub hf (integrable_const _)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, neg_sub]

variable {μ reference : Measure α} [IsProbabilityMeasure μ]
  [SigmaFinite reference] [NeZero reference] {f : α → ℝ}

/-- The exact divergence gap in the Gibbs variational bound. -/
theorem klDiv_tilted_eq_entropy_gap
    (hμ : μ ≪ reference) (hf : Integrable f μ)
    (hexp : Integrable (fun x ↦ exp (f x)) reference)
    (hlog : Integrable (llr μ reference) μ) :
    (_root_.InformationTheory.klDiv μ (reference.tilted f)).toReal =
      log (∫ x, exp (f x) ∂reference) - ∫ x, f x ∂μ - entropyWith μ reference := by
  letI := isProbabilityMeasure_tilted hexp
  rw [_root_.InformationTheory.toReal_klDiv
    (hμ.trans (absolutelyContinuous_tilted hexp))
    (integrable_llr_tilted_right hμ hf hlog hexp)]
  rw [integral_llr_tilted_right hμ hf hexp hlog]
  simp only [probReal_univ]
  unfold entropyWith
  ring

/-- Gibbs' entropy bound against any integrable exponential density. -/
theorem entropyWith_le_log_partition_sub_integral
    (hμ : μ ≪ reference) (hf : Integrable f μ)
    (hexp : Integrable (fun x ↦ exp (f x)) reference)
    (hlog : Integrable (llr μ reference) μ) :
    entropyWith μ reference ≤
      log (∫ x, exp (f x) ∂reference) - ∫ x, f x ∂μ := by
  have h := ENNReal.toReal_nonneg
    (a := _root_.InformationTheory.klDiv μ (reference.tilted f))
  rw [klDiv_tilted_eq_entropy_gap hμ hf hexp hlog] at h
  linarith

/-- Only the normalized exponential density attains the Gibbs bound. -/
theorem entropyWith_eq_log_partition_sub_integral_iff
    (hμ : μ ≪ reference) (hf : Integrable f μ)
    (hexp : Integrable (fun x ↦ exp (f x)) reference)
    (hlog : Integrable (llr μ reference) μ) :
    entropyWith μ reference =
      log (∫ x, exp (f x) ∂reference) - ∫ x, f x ∂μ ↔ μ = reference.tilted f := by
  letI := isProbabilityMeasure_tilted hexp
  have hfinite := _root_.InformationTheory.klDiv_ne_top
    (hμ.trans (absolutelyContinuous_tilted hexp))
    (integrable_llr_tilted_right hμ hf hlog hexp)
  have hzero : (_root_.InformationTheory.klDiv μ (reference.tilted f)).toReal = 0 ↔
      _root_.InformationTheory.klDiv μ (reference.tilted f) = 0 := by
    simp [ENNReal.toReal_eq_zero_iff, hfinite]
  rw [← _root_.InformationTheory.klDiv_eq_zero_iff, ← hzero,
    klDiv_tilted_eq_entropy_gap hμ hf hexp hlog]
  constructor <;> intro h <;> linarith

theorem integral_sub_log_partition_le_klDiv {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : α → ℝ}
    (hfinite : _root_.InformationTheory.klDiv μ ν ≠ ⊤)
    (hf : Integrable f μ) (hexp : Integrable (fun x ↦ exp (f x)) ν) :
    (∫ x, f x ∂μ) - log (∫ x, exp (f x) ∂ν) ≤
      (_root_.InformationTheory.klDiv μ ν).toReal := by
  obtain ⟨hac, hlog⟩ := _root_.InformationTheory.klDiv_ne_top_iff.mp hfinite
  have h := entropyWith_le_log_partition_sub_integral hac hf hexp hlog
  rw [_root_.InformationTheory.toReal_klDiv hac hlog]
  simp only [probReal_univ]
  unfold entropyWith at h
  linarith

end CapacityAtlas.MeasureInformation
