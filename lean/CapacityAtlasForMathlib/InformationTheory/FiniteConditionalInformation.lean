/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.MeasureFano
import CapacityAtlasForMathlib.InformationTheory.ConditionalDifferentialEntropy
import Mathlib.Probability.Kernel.Composition.Lemmas

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace CapacityAtlas.MeasureInformation

variable {α β υ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace υ]
  [Fintype α] [MeasurableSingletonClass α] [Fintype υ] [MeasurableSingletonClass υ]

noncomputable def finiteConditionalMutualInfo (σ : Measure υ) (ρ : υ → Measure (α × β)) : ℝ :=
  ∫ u, (mutualInfo (ρ u)).toReal ∂σ

noncomputable def finiteConditionalDecodingError
    (σ : Measure υ) (ρ : υ → Measure (α × β)) (decode : υ → β → α) : ℝ :=
  ∫ u, decodingError (ρ u) (decode u) ∂σ

omit [Fintype υ] [MeasurableSingletonClass υ] in
theorem real_compProd_finite (μ : Measure α) [IsProbabilityMeasure μ]
    (κ : Kernel α β) [IsMarkovKernel κ] (s : Set (α × β)) (hs : MeasurableSet s) :
    (μ ⊗ₘ κ).real s = ∫ a, (κ a).real (Prod.mk a ⁻¹' s) ∂μ := by
  rw [Measure.real, Measure.compProd_apply hs, lintegral_fintype,
    ENNReal.toReal_sum (by intro a _; finiteness), integral_fintype Integrable.of_finite]
  simp only [ENNReal.toReal_mul, Measure.real, smul_eq_mul, mul_comm]

omit [Fintype υ] [MeasurableSingletonClass υ] in
theorem real_comp_finite (μ : Measure α) [IsProbabilityMeasure μ]
    (κ : Kernel α β) [IsMarkovKernel κ] (s : Set β) (hs : MeasurableSet s) :
    (κ ∘ₘ μ).real s = ∫ a, (κ a).real s ∂μ := by
  rw [Measure.real, Measure.bind_apply hs (Kernel.aemeasurable _), lintegral_fintype,
    ENNReal.toReal_sum (by intro a _; finiteness), integral_fintype Integrable.of_finite]
  simp only [ENNReal.toReal_mul, Measure.real, smul_eq_mul, mul_comm]

theorem fano_finiteConditional [Nonempty α]
    (σ : Measure υ) [IsProbabilityMeasure σ] (ρ : υ → Measure (α × β))
    [∀ u, IsProbabilityMeasure (ρ u)] (decode : υ → β → α)
    (hdecode : ∀ u, Measurable (decode u))
    (huniform : ∀ u a, (ρ u).fst {a} = (Fintype.card α : ℝ≥0∞)⁻¹) :
    Real.log (Fintype.card α) ≤ finiteConditionalMutualInfo σ ρ + Real.log 2 +
      finiteConditionalDecodingError σ ρ decode * Real.log (Fintype.card α) := by
  have h := integral_mono (μ := σ) (integrable_const (Real.log (Fintype.card α)))
    (show Integrable (fun u ↦ (mutualInfo (ρ u)).toReal + Real.log 2 +
      decodingError (ρ u) (decode u) * Real.log (Fintype.card α)) σ from Integrable.of_finite)
    (fun u ↦ fano_uniform_joint_log (ρ u) (hdecode u) (huniform u))
  simpa only [integral_add (Integrable.of_finite) (Integrable.of_finite), integral_const,
    probReal_univ, one_smul, integral_mul_const, finiteConditionalMutualInfo,
    finiteConditionalDecodingError] using h

omit [Fintype υ] [MeasurableSingletonClass υ] in
theorem mutualInfo_finiteKernel_eq_entropy_sub
    (μ : Measure α) [IsProbabilityMeasure μ] (κ : Kernel α β) [IsMarkovKernel κ]
    (ν : Measure β) [SigmaFinite ν] (hac : ∀ a, κ a ≪ ν)
    (hrow : ∀ a, Integrable (llr (κ a) ν) (κ a))
    (hout : Integrable (llr (κ ∘ₘ μ) ν) (κ ∘ₘ μ)) :
    (mutualInfo (μ ⊗ₘ κ)).toReal = entropyWith (κ ∘ₘ μ) ν -
      ∫ a, entropyWith (κ a) ν ∂μ := by
  let f : α × β → ℝ≥0∞ := fun p ↦ (κ p.1).rnDeriv ν p.2
  have hf : Measurable f := measurable_from_prod_countable_right
    (fun a ↦ (κ a).measurable_rnDeriv ν)
  have hrows (a : α) : κ a = ν.withDensity (fun b ↦ f (a, b)) :=
    (Measure.withDensity_rnDeriv_eq (κ a) ν (hac a)).symm
  apply mutualInfo_compProd_eq_entropy_sub_integral μ κ ν hf hrows _ hout
  apply (Measure.integrable_compProd_iff hf.ennreal_toReal.log.aestronglyMeasurable).mpr
  exact ⟨Filter.Eventually.of_forall hrow, Integrable.of_finite⟩

omit [Fintype α] [MeasurableSingletonClass α] [Fintype υ] [MeasurableSingletonClass υ] in
theorem mutualInfo_kernel_comp_le [StandardBorelSpace α] [StandardBorelSpace β]
    {γ : Type*} [MeasurableSpace γ] (μ : Measure α) [IsProbabilityMeasure μ]
    (κ : Kernel α β) [IsMarkovKernel κ] (η : Kernel β γ) [IsMarkovKernel η] :
    mutualInfo (μ ⊗ₘ (η ∘ₖ κ)) ≤ mutualInfo (μ ⊗ₘ κ) := by
  have h := klDiv_comp_le (μ ⊗ₘ κ) (μ.prod (κ ∘ₘ μ)) (Kernel.id ∥ₖ η)
  rw [Measure.parallelComp_comp_compProd, ← Measure.prod_comp_right] at h
  simpa only [mutualInfo, Measure.fst_compProd, Measure.snd_compProd, Measure.comp_assoc] using h

theorem finiteConditionalMutualInfo_kernel_comp_le [Nonempty α] [StandardBorelSpace β]
    {γ : Type*} [MeasurableSpace γ] (σ : Measure υ) [IsProbabilityMeasure σ]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (κ : υ → Kernel α β) [∀ u, IsMarkovKernel (κ u)]
    (η : Kernel β γ) [IsMarkovKernel η]
    (huniform : ∀ a, μ {a} = (Fintype.card α : ℝ≥0∞)⁻¹) :
    finiteConditionalMutualInfo σ (fun u ↦ μ ⊗ₘ (η ∘ₖ κ u)) ≤
      finiteConditionalMutualInfo σ (fun u ↦ μ ⊗ₘ κ u) := by
  apply integral_mono Integrable.of_finite Integrable.of_finite
  intro u
  apply ENNReal.toReal_mono
  · exact mutualInfo_ne_top_of_uniform (μ ⊗ₘ κ u) (by simpa only [Measure.fst_compProd] using huniform)
  · exact mutualInfo_kernel_comp_le μ (κ u) η

theorem fano_finiteConditional_postprocess [Nonempty α] [StandardBorelSpace β]
    {γ : Type*} [MeasurableSpace γ] (σ : Measure υ) [IsProbabilityMeasure σ]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (κ : υ → Kernel α β) [∀ u, IsMarkovKernel (κ u)]
    (η : Kernel β γ) [IsMarkovKernel η] (decode : υ → γ → α)
    (hdecode : ∀ u, Measurable (decode u))
    (huniform : ∀ a, μ {a} = (Fintype.card α : ℝ≥0∞)⁻¹) :
    Real.log (Fintype.card α) ≤ finiteConditionalMutualInfo σ (fun u ↦ μ ⊗ₘ κ u) + Real.log 2 +
      finiteConditionalDecodingError σ (fun u ↦ μ ⊗ₘ (η ∘ₖ κ u)) decode *
        Real.log (Fintype.card α) := by
  have hf := fano_finiteConditional σ (fun u ↦ μ ⊗ₘ (η ∘ₖ κ u)) decode hdecode
    (fun _ ↦ by simpa only [Measure.fst_compProd] using huniform)
  have hd := finiteConditionalMutualInfo_kernel_comp_le σ μ κ η huniform
  linarith

theorem finiteConditionalMutualInfo_eq_entropy_difference
    (σ : Measure υ) [IsProbabilityMeasure σ] (μ : υ → Measure α)
    [∀ u, IsProbabilityMeasure (μ u)] (κ : υ → Kernel α β) [∀ u, IsMarkovKernel (κ u)]
    (ν : Measure β) [SigmaFinite ν] (hac : ∀ u a, κ u a ≪ ν)
    (hrow : ∀ u a, Integrable (llr (κ u a) ν) (κ u a))
    (hout : ∀ u, Integrable (llr (κ u ∘ₘ μ u) ν) (κ u ∘ₘ μ u)) :
    finiteConditionalMutualInfo σ (fun u ↦ μ u ⊗ₘ κ u) =
      (∫ u, entropyWith (κ u ∘ₘ μ u) ν ∂σ) - ∫ u, ∫ a, entropyWith (κ u a) ν ∂μ u ∂σ := by
  unfold finiteConditionalMutualInfo
  simp_rw [mutualInfo_finiteKernel_eq_entropy_sub _ _ ν (hac _) (hrow _) (hout _)]
  exact integral_sub Integrable.of_finite Integrable.of_finite

theorem fano_finiteConditional_entropy [Nonempty α]
    (σ : Measure υ) [IsProbabilityMeasure σ] (μ : Measure α) [IsProbabilityMeasure μ]
    (κ : υ → Kernel α β) [∀ u, IsMarkovKernel (κ u)] (decode : υ → β → α)
    (hdecode : ∀ u, Measurable (decode u))
    (huniform : ∀ a, μ {a} = (Fintype.card α : ℝ≥0∞)⁻¹)
    (ν : Measure β) [SigmaFinite ν] (hac : ∀ u a, κ u a ≪ ν)
    (hrow : ∀ u a, Integrable (llr (κ u a) ν) (κ u a))
    (hout : ∀ u, Integrable (llr (κ u ∘ₘ μ) ν) (κ u ∘ₘ μ)) :
    Real.log (Fintype.card α) ≤
      (∫ u, entropyWith (κ u ∘ₘ μ) ν ∂σ) - (∫ u, ∫ a, entropyWith (κ u a) ν ∂μ ∂σ) +
        Real.log 2 + finiteConditionalDecodingError σ (fun u ↦ μ ⊗ₘ κ u) decode *
          Real.log (Fintype.card α) := by
  have h := fano_finiteConditional σ (fun u ↦ μ ⊗ₘ κ u) decode hdecode
    (fun u ↦ by simpa only [Measure.fst_compProd] using huniform)
  rw [finiteConditionalMutualInfo_eq_entropy_difference σ (fun _ ↦ μ) κ ν hac hrow hout] at h
  exact h

end CapacityAtlas.MeasureInformation
