/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace CapacityAtlas.MeasureInformation

variable {α β γ δ Ω : Type*}
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ] [MeasurableSpace Ω]

/-- An injective measurable relabeling preserves all divergence, including infinity. -/
theorem klDiv_map_embedding (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : α → β} (hf : MeasurableEmbedding f) :
    klDiv (μ.map f) (ν.map f) = klDiv μ ν := by
  have hac : μ.map f ≪ ν.map f ↔ μ ≪ ν := by
    refine ⟨?_, hf.absolutelyContinuous_map⟩
    intro h s hs
    have hs' : (ν.map f) (f '' s) = 0 := by
      rwa [hf.map_apply, hf.injective.preimage_image]
    have hzero := h hs'
    rwa [hf.map_apply, hf.injective.preimage_image] at hzero
  by_cases h : μ ≪ ν
  · rw [klDiv_eq_lintegral_klFun_of_ac (hac.mpr h),
      klDiv_eq_lintegral_klFun_of_ac h, hf.lintegral_map]
    apply lintegral_congr_ae
    filter_upwards [hf.rnDeriv_map μ ν] with x hx
    rw [hx]
  · rw [klDiv_of_not_ac h, klDiv_of_not_ac (hac.not.mpr h)]

/-- Marginal divergence is bounded by joint divergence. -/
theorem klDiv_fst_le [StandardBorelSpace β]
    (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv μ.fst ν.fst ≤ klDiv μ ν := by
  cases isEmpty_or_nonempty β with
  | inl h =>
    have hμ : μ = 0 := Subsingleton.elim _ _
    have hν : ν = 0 := Subsingleton.elim _ _
    simp [hμ, hν]
  | inr h =>
    have hchain := klDiv_compProd_eq_add μ.fst ν.fst μ.condKernel ν.condKernel
    rw [μ.disintegrate μ.condKernel, ν.disintegrate ν.condKernel] at hchain
    rw [hchain]
    exact le_self_add

/-- A measurable observation cannot increase relative entropy. -/
theorem klDiv_map_le [StandardBorelSpace α] [StandardBorelSpace β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : α → β} (hf : Measurable f) :
    klDiv (μ.map f) (ν.map f) ≤ klDiv μ ν := by
  let g : α → β × α := fun x ↦ (f x, x)
  have hg : MeasurableEmbedding g := (hf.prodMk measurable_id).measurableEmbedding
    (fun _ _ h ↦ congrArg Prod.snd h)
  have h := klDiv_fst_le (μ.map g) (ν.map g)
  rw [klDiv_map_embedding μ ν hg] at h
  change klDiv (μ.map (fun x ↦ (f x, id x))).fst
    (ν.map (fun x ↦ (f x, id x))).fst ≤ _ at h
  simpa only [Measure.fst_map_prodMk (X := f) (Y := id) measurable_id] using h

theorem klDiv_snd_le [StandardBorelSpace α]
    (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv μ.snd ν.snd ≤ klDiv μ ν := by
  have h := klDiv_fst_le (μ.map Prod.swap) (ν.map Prod.swap)
  rw [klDiv_map_embedding (f := Prod.swap) μ ν
    MeasurableEquiv.prodComm.measurableEmbedding] at h
  simpa only [Measure.fst_map_swap] using h

/-- A common stochastic processing kernel cannot increase relative entropy. -/
theorem klDiv_comp_le [StandardBorelSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    klDiv (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ klDiv μ ν := by
  have h := klDiv_snd_le (μ ⊗ₘ κ) (ν ⊗ₘ κ)
  simpa only [Measure.snd_compProd, klDiv_compProd_left] using h

/-- Mutual information of a joint law, with infinite values retained. -/
noncomputable def mutualInfo (ρ : Measure (α × β)) : ℝ≥0∞ :=
  klDiv ρ (ρ.fst.prod ρ.snd)

/-- Mutual information of two observations of the same experiment. -/
noncomputable def mutualInfoRV (X : Ω → α) (Y : Ω → β) (μ : Measure Ω) : ℝ≥0∞ :=
  mutualInfo (μ.map (fun ω ↦ (X ω, Y ω)))

theorem mutualInfo_nonneg (ρ : Measure (α × β)) : 0 ≤ mutualInfo ρ := zero_le

theorem mutualInfo_eq_zero_iff (ρ : Measure (α × β)) [IsFiniteMeasure ρ] :
    mutualInfo ρ = 0 ↔ ρ = ρ.fst.prod ρ.snd := klDiv_eq_zero_iff

theorem mutualInfo_prod (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : mutualInfo (μ.prod ν) = 0 := by
  simp [mutualInfo, Measure.fst_prod, Measure.snd_prod]

theorem mutualInfo_swap (ρ : Measure (α × β)) [IsFiniteMeasure ρ] :
    mutualInfo (ρ.map Prod.swap) = mutualInfo ρ := by
  simp only [mutualInfo, Measure.fst_map_swap, Measure.snd_map_swap]
  rw [← Measure.prod_swap]
  exact klDiv_map_embedding ρ (ρ.fst.prod ρ.snd)
    MeasurableEquiv.prodComm.measurableEmbedding

private theorem fst_map_prodMap (ρ : Measure (α × β))
    {f : α → γ} {g : β → δ} (hf : Measurable f) (hg : Measurable g) :
    (ρ.map (Prod.map f g)).fst = ρ.fst.map f := by
  change (ρ.map (Prod.map f g)).map Prod.fst = (ρ.map Prod.fst).map f
  rw [Measure.map_map measurable_fst (hf.prodMap hg), Measure.map_map hf measurable_fst]
  rfl

private theorem snd_map_prodMap (ρ : Measure (α × β))
    {f : α → γ} {g : β → δ} (hf : Measurable f) (hg : Measurable g) :
    (ρ.map (Prod.map f g)).snd = ρ.snd.map g := by
  change (ρ.map (Prod.map f g)).map Prod.snd = (ρ.map Prod.snd).map g
  rw [Measure.map_map measurable_snd (hf.prodMap hg), Measure.map_map hg measurable_snd]
  rfl

/-- Processing either component cannot increase their mutual information. -/
theorem mutualInfo_map_le [StandardBorelSpace α] [StandardBorelSpace β]
    [StandardBorelSpace γ] [StandardBorelSpace δ]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ]
    {f : α → γ} {g : β → δ} (hf : Measurable f) (hg : Measurable g) :
    mutualInfo (ρ.map (Prod.map f g)) ≤ mutualInfo ρ := by
  simp only [mutualInfo, fst_map_prodMap ρ hf hg, snd_map_prodMap ρ hf hg,
    Measure.map_prod_map ρ.fst ρ.snd hf hg]
  exact klDiv_map_le ρ (ρ.fst.prod ρ.snd) (hf.prodMap hg)

theorem mutualInfo_map_embedding (ρ : Measure (α × β)) [IsFiniteMeasure ρ]
    {f : α → γ} {g : β → δ} (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g) :
    mutualInfo (ρ.map (Prod.map f g)) = mutualInfo ρ := by
  simp only [mutualInfo, fst_map_prodMap ρ hf.measurable hg.measurable,
    snd_map_prodMap ρ hf.measurable hg.measurable,
    Measure.map_prod_map ρ.fst ρ.snd hf.measurable hg.measurable]
  exact klDiv_map_embedding ρ (ρ.fst.prod ρ.snd) (hf.prodMap hg)

theorem mutualInfoRV_eq_klDiv (μ : Measure Ω) {X : Ω → α} {Y : Ω → β}
    (hX : Measurable X) (hY : Measurable Y) :
    mutualInfoRV X Y μ =
      klDiv (μ.map (fun ω ↦ (X ω, Y ω))) ((μ.map X).prod (μ.map Y)) := by
  rw [mutualInfoRV, mutualInfo, Measure.fst_map_prodMk hY, Measure.snd_map_prodMk hX]

theorem mutualInfoRV_eq_zero_iff (μ : Measure Ω) [IsFiniteMeasure μ]
    {X : Ω → α} {Y : Ω → β} (hX : Measurable X) (hY : Measurable Y) :
    mutualInfoRV X Y μ = 0 ↔ IndepFun X Y μ := by
  rw [mutualInfoRV_eq_klDiv μ hX hY, klDiv_eq_zero_iff,
    indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable]

theorem mutualInfoRV_symm (μ : Measure Ω) [IsFiniteMeasure μ]
    {X : Ω → α} {Y : Ω → β} (hX : Measurable X) (hY : Measurable Y) :
    mutualInfoRV X Y μ = mutualInfoRV Y X μ := by
  have h := mutualInfo_swap (μ.map (fun ω ↦ (X ω, Y ω)))
  rw [Measure.map_map measurable_swap (hX.prodMk hY)] at h
  exact h.symm

theorem mutualInfoRV_comp_le [StandardBorelSpace α] [StandardBorelSpace β]
    [StandardBorelSpace γ] [StandardBorelSpace δ]
    (μ : Measure Ω) [IsFiniteMeasure μ] {X : Ω → α} {Y : Ω → β}
    {f : α → γ} {g : β → δ}
    (hX : Measurable X) (hY : Measurable Y) (hf : Measurable f) (hg : Measurable g) :
    mutualInfoRV (f ∘ X) (g ∘ Y) μ ≤ mutualInfoRV X Y μ := by
  have h := mutualInfo_map_le (μ.map (fun ω ↦ (X ω, Y ω))) hf hg
  rw [Measure.map_map (hf.prodMap hg) (hX.prodMk hY)] at h
  exact h

/-- A measurable decoder cannot extract more information than its observation contains. -/
theorem mutualInfoRV_decoder_le [StandardBorelSpace α] [StandardBorelSpace β]
    [StandardBorelSpace γ] (μ : Measure Ω) [IsFiniteMeasure μ]
    {X : Ω → α} {Y : Ω → β} {decode : β → γ}
    (hX : Measurable X) (hY : Measurable Y) (hdecode : Measurable decode) :
    mutualInfoRV X (decode ∘ Y) μ ≤ mutualInfoRV X Y μ :=
  mutualInfoRV_comp_le μ hX hY measurable_id hdecode

theorem mutualInfoRV_comp_embedding (μ : Measure Ω) [IsFiniteMeasure μ]
    {X : Ω → α} {Y : Ω → β} {f : α → γ} {g : β → δ}
    (hX : Measurable X) (hY : Measurable Y)
    (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g) :
    mutualInfoRV (f ∘ X) (g ∘ Y) μ = mutualInfoRV X Y μ := by
  have h := mutualInfo_map_embedding (μ.map (fun ω ↦ (X ω, Y ω))) hf hg
  rw [Measure.map_map (hf.measurable.prodMap hg.measurable) (hX.prodMk hY)] at h
  exact h

end CapacityAtlas.MeasureInformation
