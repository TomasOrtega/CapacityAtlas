/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteConditionalInformation
import CapacityAtlasForMathlib.InformationTheory.GaussianMixtureEntropy
import CapacityAtlasForMathlib.InformationTheory.GaussianMixtureMeasure

open MeasureTheory ProbabilityTheory InformationTheory Matrix
open scoped ENNReal

namespace CapacityAtlas.MeasureInformation

variable {α β υ ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace υ]
  [Fintype α] [Fintype β] [Fintype υ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass υ]
  [Fintype ι] [DecidableEq ι]

noncomputable def gaussianCodebookKernel (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) :
    Kernel α (EuclideanSpace ℝ ι) :=
  Kernel.ofFunOfCountable (fun a ↦ multivariateGaussian (m a) N)

instance gaussianCodebookKernel_isMarkovKernel (m : α → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) : IsMarkovKernel (gaussianCodebookKernel m N) :=
  ⟨fun _ ↦ inferInstanceAs (IsProbabilityMeasure (multivariateGaussian _ _))⟩

@[simp] theorem gaussianCodebookKernel_apply (m : α → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (a : α) : gaussianCodebookKernel m N a = multivariateGaussian (m a) N := rfl

theorem sum_real_singleton_eq_one (μ : Measure α) [IsProbabilityMeasure μ] :
    ∑ a, μ.real {a} = 1 := by simp

theorem gaussianCodebookKernel_comp_eq_mixture (μ : Measure α) [IsProbabilityMeasure μ]
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) :
    gaussianCodebookKernel m N ∘ₘ μ = gaussianMixtureMeasure (fun a ↦ μ.real {a}) m N := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), lintegral_fintype]
  simp only [gaussianMixtureMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _),
    gaussianCodebookKernel_apply]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

theorem gaussianCodebookKernel_output_ac (μ : Measure α) [IsProbabilityMeasure μ]
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef) :
    gaussianCodebookKernel m N ∘ₘ μ ≪ volume :=
  gaussianMixture_absolutelyContinuous μ _ m N hN (fun _ ↦ rfl)

theorem gaussianCodebookKernel_comp_map (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (m : β → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) :
    gaussianCodebookKernel m N ∘ₘ μ.map f = gaussianCodebookKernel (m ∘ f) N ∘ₘ μ := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_map ((gaussianCodebookKernel m N).measurable_coe hs) (measurable_of_countable f)]
  rfl

theorem gaussianCodebookKernel_output_integrable_llr (μ : Measure α) [IsProbabilityMeasure μ]
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef) :
    Integrable (llr (gaussianCodebookKernel m N ∘ₘ μ) volume)
      (gaussianCodebookKernel m N ∘ₘ μ) :=
  integrable_llr_gaussianMixture_volume μ _ m N hN (fun _ ↦ rfl)

noncomputable def gaussianMarginalCodebookKernel (ν : Measure β)
    (m : α → β → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) :
    Kernel α (EuclideanSpace ℝ ι) :=
  Kernel.ofFunOfCountable (fun a ↦ gaussianCodebookKernel (m a) N ∘ₘ ν)

instance gaussianMarginalCodebookKernel_isMarkovKernel (ν : Measure β) [IsProbabilityMeasure ν]
    (m : α → β → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) :
    IsMarkovKernel (gaussianMarginalCodebookKernel ν m N) :=
  ⟨fun _ ↦ inferInstanceAs (IsProbabilityMeasure (gaussianCodebookKernel _ _ ∘ₘ ν))⟩

@[simp] theorem gaussianMarginalCodebookKernel_apply (ν : Measure β)
    (m : α → β → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (a : α) :
    gaussianMarginalCodebookKernel ν m N a = gaussianCodebookKernel (m a) N ∘ₘ ν := rfl

theorem gaussianMarginalCodebookKernel_comp (μ : Measure α) [IsProbabilityMeasure μ]
    (ν : Measure β) [IsProbabilityMeasure ν]
    (m : α → β → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) :
    gaussianMarginalCodebookKernel ν m N ∘ₘ μ =
      gaussianCodebookKernel (fun p : α × β ↦ m p.1 p.2) N ∘ₘ μ.prod ν := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_prod _ (measurable_of_countable _).aemeasurable]
  apply lintegral_congr
  intro a
  rw [gaussianMarginalCodebookKernel_apply, Measure.bind_apply hs (Kernel.aemeasurable _)]
  rfl

theorem mutualInfo_gaussianMarginalCodebookKernel (μ : Measure α) [IsProbabilityMeasure μ]
    (ν : Measure β) [IsProbabilityMeasure ν]
    (m : α → β → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef) :
    (mutualInfo (μ ⊗ₘ gaussianMarginalCodebookKernel ν m N)).toReal =
      entropyWith (gaussianCodebookKernel (fun p : α × β ↦ m p.1 p.2) N ∘ₘ μ.prod ν) volume -
        ∫ a, entropyWith (gaussianCodebookKernel (m a) N ∘ₘ ν) volume ∂μ := by
  rw [mutualInfo_finiteKernel_eq_entropy_sub μ _ volume]
  · rw [gaussianMarginalCodebookKernel_comp]
    rfl
  · exact fun a ↦ gaussianCodebookKernel_output_ac ν (m a) N hN
  · exact fun a ↦ gaussianCodebookKernel_output_integrable_llr ν (m a) N hN
  · rw [gaussianMarginalCodebookKernel_comp]
    exact gaussianCodebookKernel_output_integrable_llr _ _ N hN

theorem decodingError_gaussianMarginalCodebookKernel
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
    (m : α → β → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ)
    (decode : EuclideanSpace ℝ ι → α) (hdecode : Measurable decode) :
    decodingError (μ ⊗ₘ gaussianMarginalCodebookKernel ν m N) decode =
      ∫ a, ∫ b, (multivariateGaussian (m a b) N).real {y | decode y ≠ a} ∂ν ∂μ := by
  have hs : MeasurableSet {p : α × EuclideanSpace ℝ ι | decode p.2 ≠ p.1} :=
    (measurableSet_eq_fun (hdecode.comp measurable_snd) measurable_fst).compl
  rw [decodingError, real_compProd_finite μ _ _ hs]
  apply integral_congr_ae
  filter_upwards with a
  have ht : MeasurableSet {y | decode y ≠ a} :=
    ((measurableSet_singleton a).preimage hdecode).compl
  change (gaussianCodebookKernel (m a) N ∘ₘ ν).real {y | decode y ≠ a} = _
  rw [real_comp_finite ν _ _ ht]
  rfl

theorem decodingError_postprocess_gaussianMarginalCodebookKernel
    {γ : Type*} [MeasurableSpace γ]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
    (m : α → β → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ)
    (η : Kernel (EuclideanSpace ℝ ι) γ) [IsMarkovKernel η]
    (decode : γ → α) (hdecode : Measurable decode) :
    decodingError (μ ⊗ₘ (η ∘ₖ gaussianMarginalCodebookKernel ν m N)) decode =
      ∫ a, ∫ b, (η ∘ₘ multivariateGaussian (m a b) N).real {y | decode y ≠ a} ∂ν ∂μ := by
  have hs : MeasurableSet {p : α × γ | decode p.2 ≠ p.1} :=
    (measurableSet_eq_fun (hdecode.comp measurable_snd) measurable_fst).compl
  rw [decodingError, real_compProd_finite μ _ _ hs]
  apply integral_congr_ae
  filter_upwards with a
  have ht : MeasurableSet {y | decode y ≠ a} :=
    ((measurableSet_singleton a).preimage hdecode).compl
  change (η ∘ₘ (gaussianCodebookKernel (m a) N ∘ₘ ν)).real {y | decode y ≠ a} = _
  rw [Measure.comp_assoc, real_comp_finite ν _ _ ht]
  rfl

theorem fano_gaussianFiniteConditioning [Nonempty α]
    (σ : Measure υ) [IsProbabilityMeasure σ]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
    (m : υ → α → β → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (decode : υ → EuclideanSpace ℝ ι → α) (hdecode : ∀ u, Measurable (decode u))
    (huniform : ∀ a, μ {a} = (Fintype.card α : ℝ≥0∞)⁻¹) :
    Real.log (Fintype.card α) ≤
      (∫ u, entropyWith (gaussianCodebookKernel (fun p : α × β ↦ m u p.1 p.2) N ∘ₘ μ.prod ν)
        volume ∂σ) - (∫ u, ∫ a, entropyWith (gaussianCodebookKernel (m u a) N ∘ₘ ν) volume ∂μ ∂σ) +
      Real.log 2 + finiteConditionalDecodingError σ
        (fun u ↦ μ ⊗ₘ gaussianMarginalCodebookKernel ν (m u) N) decode *
          Real.log (Fintype.card α) := by
  have h := fano_finiteConditional σ (fun u ↦ μ ⊗ₘ gaussianMarginalCodebookKernel ν (m u) N)
    decode hdecode (fun _ ↦ by simpa only [Measure.fst_compProd] using huniform)
  unfold finiteConditionalMutualInfo at h
  simp_rw [mutualInfo_gaussianMarginalCodebookKernel μ ν _ N hN] at h
  rwa [integral_sub Integrable.of_finite Integrable.of_finite] at h

end CapacityAtlas.MeasureInformation
