/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.MeasureInformation
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal

namespace CapacityAtlas.MeasureInformation

variable {α β Ω : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace Ω]

/-- A bounded density has integrable log-likelihood ratio under its own law. -/
theorem integrable_llr_of_le_smul (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (hdom : μ ≤ C • ν) : Integrable (llr μ ν) μ := by
  have hac : μ ≪ ν := Measure.absolutelyContinuous_of_le_smul hdom
  have hbound : μ.rnDeriv ν ≤ᵐ[ν] fun _ ↦ C := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ.measurable_rnDeriv ν)
      fun s _ _ ↦ ?_
    simpa using (Measure.setLIntegral_rnDeriv_le (μ := μ) (ν := ν) s).trans (hdom s)
  have hcont : Continuous (fun x : ℝ ↦ ‖x * log x‖) := continuous_mul_log.norm
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := C.toReal)).bddAbove_image hcont.continuousOn
  apply (integrable_rnDeriv_mul_log_iff hac).mp
  refine (integrable_const M).mono' ?_ ?_
  · exact (continuous_mul_log.measurable.comp
      (μ.measurable_rnDeriv ν).ennreal_toReal).aestronglyMeasurable
  · filter_upwards [hbound] with x hx
    apply hM
    exact ⟨(μ.rnDeriv ν x).toReal,
      ⟨ENNReal.toReal_nonneg, ENNReal.toReal_mono hC hx⟩, rfl⟩

theorem klDiv_ne_top_of_le_smul (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (hdom : μ ≤ C • ν) : klDiv μ ν ≠ ⊤ :=
  klDiv_ne_top_iff.mpr ⟨Measure.absolutelyContinuous_of_le_smul hdom,
    integrable_llr_of_le_smul μ ν hC hdom⟩

/-- Domination of probability measures bounds relative entropy by the log density bound. -/
theorem toReal_klDiv_le_log_of_le_smul (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (hdom : μ ≤ C • ν) : (klDiv μ ν).toReal ≤ log C.toReal := by
  have hac : μ ≪ ν := Measure.absolutelyContinuous_of_le_smul hdom
  have hbound : μ.rnDeriv ν ≤ᵐ[ν] fun _ ↦ C := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ.measurable_rnDeriv ν)
      fun s _ _ ↦ ?_
    simpa using (Measure.setLIntegral_rnDeriv_le (μ := μ) (ν := ν) s).trans (hdom s)
  have hint := integrable_llr_of_le_smul μ ν hC hdom
  have hlog : llr μ ν ≤ᵐ[μ] fun _ ↦ log C.toReal := by
    filter_upwards [hac.ae_le hbound, Measure.rnDeriv_pos hac] with x hx hpos
    exact log_le_log (ENNReal.toReal_pos hpos.ne' (ne_top_of_le_ne_top hC hx))
      (ENNReal.toReal_mono hC hx)
  simpa [toReal_klDiv hac hint] using integral_mono_ae hint (integrable_const _) hlog

section FiniteMessages

variable [Fintype α] [MeasurableSingletonClass α] [Nonempty α]

/-- A uniform finite message bounds the joint law by the product of its marginals. -/
theorem joint_le_card_smul_prod (ρ : Measure (α × β)) [IsProbabilityMeasure ρ]
    (huniform : ∀ m, ρ.fst {m} = (Fintype.card α : ℝ≥0∞)⁻¹) :
    ρ ≤ (Fintype.card α : ℝ≥0∞) • (ρ.fst.prod ρ.snd) := by
  classical
  apply Measure.le_iff.mpr
  intro s hs
  have hcover : s = ⋃ m : α, {p : α × β | p.1 = m ∧ p ∈ s} := by
    ext p
    simp
  have hsum : ρ s ≤ ∑ m : α, ρ.snd (Prod.mk m ⁻¹' s) := by
    nth_rw 1 [hcover]
    apply (measure_iUnion_fintype_le ρ _).trans
    apply Finset.sum_le_sum
    intro m _
    rw [Measure.snd_apply (measurable_prodMk_left hs)]
    exact measure_mono (by rintro ⟨a, b⟩ ⟨rfl, hp⟩; exact hp)
  have hcard : (Fintype.card α : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [Measure.smul_apply, smul_eq_mul, Measure.prod_apply hs, lintegral_fintype]
  simp_rw [huniform]
  rw [← Finset.sum_mul, ← mul_assoc, mul_comm (Fintype.card α : ℝ≥0∞), mul_assoc,
    ENNReal.mul_inv_cancel hcard (by simp), mul_one]
  exact hsum

theorem mutualInfo_ne_top_of_uniform (ρ : Measure (α × β)) [IsProbabilityMeasure ρ]
    (huniform : ∀ m, ρ.fst {m} = (Fintype.card α : ℝ≥0∞)⁻¹) :
    mutualInfo ρ ≠ ⊤ :=
  klDiv_ne_top_of_le_smul ρ (ρ.fst.prod ρ.snd) (by simp)
    (joint_le_card_smul_prod ρ huniform)

theorem mutualInfo_toReal_le_log_card (ρ : Measure (α × β)) [IsProbabilityMeasure ρ]
    (huniform : ∀ m, ρ.fst {m} = (Fintype.card α : ℝ≥0∞)⁻¹) :
    (mutualInfo ρ).toReal ≤ log (Fintype.card α) := by
  simpa [mutualInfo] using toReal_klDiv_le_log_of_le_smul ρ (ρ.fst.prod ρ.snd)
    (by simp) (joint_le_card_smul_prod ρ huniform)

theorem mutualInfo_le_log_card (ρ : Measure (α × β)) [IsProbabilityMeasure ρ]
    (huniform : ∀ m, ρ.fst {m} = (Fintype.card α : ℝ≥0∞)⁻¹) :
    mutualInfo ρ ≤ ENNReal.ofReal (log (Fintype.card α)) := by
  rw [← ENNReal.ofReal_toReal (mutualInfo_ne_top_of_uniform ρ huniform)]
  exact ENNReal.ofReal_le_ofReal (mutualInfo_toReal_le_log_card ρ huniform)

theorem mutualInfoRV_ne_top_of_uniform (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → α} {Y : Ω → β} (hX : Measurable X) (hY : Measurable Y)
    (huniform : ∀ m, (μ.map X) {m} = (Fintype.card α : ℝ≥0∞)⁻¹) :
    mutualInfoRV X Y μ ≠ ⊤ := by
  letI : IsProbabilityMeasure (μ.map (fun ω ↦ (X ω, Y ω))) :=
    Measure.isProbabilityMeasure_map (hX.prodMk hY).aemeasurable
  apply mutualInfo_ne_top_of_uniform
  simpa only [Measure.fst_map_prodMk hY] using huniform

theorem mutualInfoRV_toReal_le_log_card (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → α} {Y : Ω → β} (hX : Measurable X) (hY : Measurable Y)
    (huniform : ∀ m, (μ.map X) {m} = (Fintype.card α : ℝ≥0∞)⁻¹) :
    (mutualInfoRV X Y μ).toReal ≤ log (Fintype.card α) := by
  letI : IsProbabilityMeasure (μ.map (fun ω ↦ (X ω, Y ω))) :=
    Measure.isProbabilityMeasure_map (hX.prodMk hY).aemeasurable
  apply mutualInfo_toReal_le_log_card
  simpa only [Measure.fst_map_prodMk hY] using huniform

end FiniteMessages

end CapacityAtlas.MeasureInformation
