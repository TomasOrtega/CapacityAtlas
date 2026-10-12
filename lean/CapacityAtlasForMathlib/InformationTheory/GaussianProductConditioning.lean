/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianFiniteConditioning
import CapacityAtlasForMathlib.MeasureTheory.PiResampling

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace CapacityAtlas.MeasureInformation

variable {K : ℕ} {M : Fin K → Type*}

def prefixMessage (k : ℕ) (u x : ∀ i, M i) : ∀ i, M i :=
  spliceProduct (fun i : Fin K ↦ i.val < k) x u

theorem prefixMessage_zero (u x : ∀ i, M i) : prefixMessage 0 u x = u := by
  ext i
  simp [prefixMessage, spliceProduct]

theorem prefixMessage_all (u x : ∀ i, M i) : prefixMessage K u x = x := by
  ext i
  simp [prefixMessage, spliceProduct, i.isLt]

theorem prefixMessage_update_current (i : Fin K) (u x : ∀ j, M j) (a : M i) :
    prefixMessage i.val (Function.update u i a) x i = a := by
  simp [prefixMessage, spliceProduct]

theorem prefixMessage_succ_update (i : Fin K) (u x : ∀ j, M j) (a : M i) :
    prefixMessage (i.val + 1) u (Function.update x i a) =
      prefixMessage i.val (Function.update u i a) x := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [prefixMessage, spliceProduct]
  · have hv : j.val ≠ i.val := fun h ↦ hji (Fin.ext h)
    have hl : j.val < i.val + 1 ↔ j.val < i.val := by omega
    simp [prefixMessage, spliceProduct, hji, hl]

variable [∀ i, MeasurableSpace (M i)] [∀ i, Fintype (M i)]
  [∀ i, MeasurableSingletonClass (M i)] {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def prefixGaussianLaw (μ : (i : Fin K) → Measure (M i))
    (f : (∀ i, M i) → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (k : ℕ) (u : ∀ i, M i) :
    Measure (EuclideanSpace ℝ ι) :=
  gaussianCodebookKernel (fun x ↦ f (prefixMessage k u x)) N ∘ₘ Measure.pi μ

instance prefixGaussianLaw_isProbabilityMeasure (μ : (i : Fin K) → Measure (M i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : (∀ i, M i) → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (k : ℕ) (u : ∀ i, M i) : IsProbabilityMeasure (prefixGaussianLaw μ f N k u) := by
  unfold prefixGaussianLaw
  infer_instance

noncomputable def prefixGaussianEntropy (μ : (i : Fin K) → Measure (M i))
    (f : (∀ i, M i) → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (k : ℕ) : ℝ :=
  ∫ u, entropyWith (prefixGaussianLaw μ f N k u) volume ∂Measure.pi μ

theorem prefixGaussianLaw_zero (μ : (i : Fin K) → Measure (M i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : (∀ i, M i) → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (u : ∀ i, M i) :
    prefixGaussianLaw μ f N 0 u = multivariateGaussian (f u) N := by
  ext s hs
  rw [prefixGaussianLaw, Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp only [gaussianCodebookKernel_apply, prefixMessage_zero, lintegral_const,
    measure_univ, mul_one]

theorem prefixGaussianEntropy_zero (μ : (i : Fin K) → Measure (M i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : (∀ i, M i) → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) :
    prefixGaussianEntropy μ f N 0 = entropyWith (multivariateGaussian 0 N) volume := by
  simp only [prefixGaussianEntropy, prefixGaussianLaw_zero,
    entropyWith_multivariateGaussian _ N hN, integral_const, probReal_univ, one_smul]

theorem prefixGaussianEntropy_all (μ : (i : Fin K) → Measure (M i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : (∀ i, M i) → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) :
    prefixGaussianEntropy μ f N K = entropyWith (gaussianCodebookKernel f N ∘ₘ Measure.pi μ) volume := by
  simp only [prefixGaussianEntropy, prefixGaussianLaw, prefixMessage_all,
    integral_const, probReal_univ, one_smul]

theorem prefixGaussianLaw_succ (μ : (i : Fin K) → Measure (M i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : (∀ i, M i) → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (i : Fin K) (u : ∀ j, M j) :
    gaussianCodebookKernel (fun z : M i × (∀ j, M j) ↦
      f (prefixMessage i.val (Function.update u i z.1) z.2)) N ∘ₘ (μ i).prod (Measure.pi μ) =
        prefixGaussianLaw μ f N (i.val + 1) u := by
  have he := (measurePreserving_updateProduct μ i).map_eq
  conv_rhs => rw [prefixGaussianLaw, ← he, gaussianCodebookKernel_comp_map]
  simp only [Function.comp_def, prefixMessage_succ_update]

theorem prefixGaussianEntropy_update (μ : (i : Fin K) → Measure (M i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : (∀ i, M i) → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (i : Fin K) :
    (∫ u, ∫ a, entropyWith (prefixGaussianLaw μ f N i.val (Function.update u i a)) volume
      ∂μ i ∂Measure.pi μ) = prefixGaussianEntropy μ f N i.val := by
  rw [integral_integral_swap Integrable.of_finite]
  exact integral_updateProduct μ i (fun u ↦ entropyWith (prefixGaussianLaw μ f N i.val u) volume)

theorem integral_prefixMessage_update (μ : (i : Fin K) → Measure (M i))
    [∀ i, IsProbabilityMeasure (μ i)] (i : Fin K) (g : (∀ j, M j) → ℝ) :
    (∫ u, ∫ a, ∫ x, g (prefixMessage i.val (Function.update u i a) x)
      ∂Measure.pi μ ∂μ i ∂Measure.pi μ) = ∫ z, g z ∂Measure.pi μ := by
  have hs (u : ∀ j, M j) : (∫ a, ∫ x, g (prefixMessage i.val (Function.update u i a) x)
      ∂Measure.pi μ ∂μ i) = ∫ x, ∫ a, g (prefixMessage i.val (Function.update u i a) x)
        ∂μ i ∂Measure.pi μ := integral_integral_swap Integrable.of_finite
  simp_rw [hs]
  rw [integral_integral_swap Integrable.of_finite]
  have hu (x : ∀ j, M j) : (∫ u, ∫ a, g (prefixMessage i.val (Function.update u i a) x)
      ∂μ i ∂Measure.pi μ) = ∫ u, g (prefixMessage i.val u x) ∂Measure.pi μ := by
    rw [integral_integral_swap Integrable.of_finite]
    exact integral_updateProduct μ i (fun u ↦ g (prefixMessage i.val u x))
  simp_rw [hu]
  exact integral_spliceProduct μ (fun j ↦ j.val < i.val) g

theorem finiteConditionalDecodingError_prefixGaussian (μ : (i : Fin K) → Measure (M i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : (∀ i, M i) → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (i : Fin K) (decode : EuclideanSpace ℝ ι → M i)
    (hdecode : Measurable decode) :
    finiteConditionalDecodingError (Measure.pi μ) (fun u ↦ μ i ⊗ₘ
      gaussianMarginalCodebookKernel (Measure.pi μ)
        (fun a x ↦ f (prefixMessage i.val (Function.update u i a) x)) N) (fun _ ↦ decode) =
      ∫ z, (multivariateGaussian (f z) N).real {y | decode y ≠ z i} ∂Measure.pi μ := by
  unfold finiteConditionalDecodingError
  simp_rw [decodingError_gaussianMarginalCodebookKernel _ _ _ _ decode hdecode]
  have he := integral_prefixMessage_update μ i
    (fun z ↦ (multivariateGaussian (f z) N).real {y | decode y ≠ z i})
  simpa only [prefixMessage_update_current] using he

theorem fano_prefixGaussian [∀ i, Nonempty (M i)]
    (μ : (i : Fin K) → Measure (M i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, M i) → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (i : Fin K) (decode : EuclideanSpace ℝ ι → M i) (hdecode : Measurable decode)
    (huniform : ∀ a, μ i {a} = (Fintype.card (M i) : ℝ≥0∞)⁻¹) :
    Real.log (Fintype.card (M i)) ≤
      prefixGaussianEntropy μ f N (i.val + 1) - prefixGaussianEntropy μ f N i.val + Real.log 2 +
        (∫ z, (multivariateGaussian (f z) N).real {y | decode y ≠ z i} ∂Measure.pi μ) *
          Real.log (Fintype.card (M i)) := by
  have h := fano_gaussianFiniteConditioning (Measure.pi μ) (μ i) (Measure.pi μ)
    (fun u a x ↦ f (prefixMessage i.val (Function.update u i a) x)) N hN
    (fun _ ↦ decode) (fun _ ↦ hdecode) huniform
  simp_rw [prefixGaussianLaw_succ] at h
  change Real.log _ ≤ prefixGaussianEntropy μ f N (i.val + 1) -
    (∫ u, ∫ a, entropyWith (prefixGaussianLaw μ f N i.val (Function.update u i a)) volume
      ∂μ i ∂Measure.pi μ) + Real.log 2 + _ at h
  rw [prefixGaussianEntropy_update, finiteConditionalDecodingError_prefixGaussian μ f N i decode hdecode] at h
  exact h

theorem finiteConditionalMutualInfo_prefixGaussian_eq
    (μ : (i : Fin K) → Measure (M i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, M i) → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef) (i : Fin K) :
    finiteConditionalMutualInfo (Measure.pi μ) (fun u ↦ μ i ⊗ₘ
      gaussianMarginalCodebookKernel (Measure.pi μ)
        (fun a x ↦ f (prefixMessage i.val (Function.update u i a) x)) N) =
      prefixGaussianEntropy μ f N (i.val + 1) - prefixGaussianEntropy μ f N i.val := by
  unfold finiteConditionalMutualInfo
  simp_rw [mutualInfo_gaussianMarginalCodebookKernel _ _ _ N hN, prefixGaussianLaw_succ]
  rw [integral_sub Integrable.of_finite Integrable.of_finite]
  exact congrArg (prefixGaussianEntropy μ f N (i.val + 1) - ·) (prefixGaussianEntropy_update μ f N i)

theorem finiteConditionalDecodingError_postprocess_prefixGaussian
    {β : Type*} [MeasurableSpace β]
    (μ : (i : Fin K) → Measure (M i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, M i) → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ)
    (η : Kernel (EuclideanSpace ℝ ι) β) [IsMarkovKernel η]
    (i : Fin K) (decode : β → M i) (hdecode : Measurable decode) :
    finiteConditionalDecodingError (Measure.pi μ) (fun u ↦ μ i ⊗ₘ
      (η ∘ₖ gaussianMarginalCodebookKernel (Measure.pi μ)
        (fun a x ↦ f (prefixMessage i.val (Function.update u i a) x)) N)) (fun _ ↦ decode) =
      ∫ z, (η ∘ₘ multivariateGaussian (f z) N).real {y | decode y ≠ z i} ∂Measure.pi μ := by
  unfold finiteConditionalDecodingError
  simp_rw [decodingError_postprocess_gaussianMarginalCodebookKernel _ _ _ _ η decode hdecode]
  have he := integral_prefixMessage_update μ i
    (fun z ↦ (η ∘ₘ multivariateGaussian (f z) N).real {y | decode y ≠ z i})
  simpa only [prefixMessage_update_current] using he

theorem fano_postprocess_prefixGaussian [∀ i, Nonempty (M i)]
    {β : Type*} [MeasurableSpace β]
    (μ : (i : Fin K) → Measure (M i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, M i) → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (η : Kernel (EuclideanSpace ℝ ι) β) [IsMarkovKernel η]
    (i : Fin K) (decode : β → M i) (hdecode : Measurable decode)
    (huniform : ∀ a, μ i {a} = (Fintype.card (M i) : ℝ≥0∞)⁻¹) :
    Real.log (Fintype.card (M i)) ≤
      prefixGaussianEntropy μ f N (i.val + 1) - prefixGaussianEntropy μ f N i.val + Real.log 2 +
        (∫ z, (η ∘ₘ multivariateGaussian (f z) N).real {y | decode y ≠ z i} ∂Measure.pi μ) *
          Real.log (Fintype.card (M i)) := by
  have h := fano_finiteConditional_postprocess (Measure.pi μ) (μ i)
    (fun u ↦ gaussianMarginalCodebookKernel (Measure.pi μ)
      (fun a x ↦ f (prefixMessage i.val (Function.update u i a) x)) N)
    η (fun _ ↦ decode) (fun _ ↦ hdecode) huniform
  rw [finiteConditionalMutualInfo_prefixGaussian_eq μ f N hN i,
    finiteConditionalDecodingError_postprocess_prefixGaussian μ f N η i decode hdecode] at h
  exact h

end CapacityAtlas.MeasureInformation
