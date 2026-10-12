/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianFiniteConditioning
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open MeasureTheory ProbabilityTheory InformationTheory Matrix
open scoped ENNReal

namespace CapacityAtlas.MeasureInformation

variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]

section MeasurableLabels

variable [MeasurableSpace α] [MeasurableSingletonClass α]

noncomputable def finiteWeightLaw (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1) :
    Measure α :=
  (PMF.ofFintype (fun a ↦ ENNReal.ofReal (w a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ ↦ hw a), hw1, ENNReal.ofReal_one])).toMeasure

instance finiteWeightLaw_isProbabilityMeasure (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hw1 : ∑ a, w a = 1) : IsProbabilityMeasure (finiteWeightLaw w hw hw1) := by
  unfold finiteWeightLaw
  infer_instance

theorem finiteWeightLaw_real_singleton (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hw1 : ∑ a, w a = 1) (a : α) : (finiteWeightLaw w hw hw1).real {a} = w a := by
  rw [Measure.real, finiteWeightLaw, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]
  exact ENNReal.toReal_ofReal (hw a)

theorem gaussianMixtureMeasure_eq_codebook (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hw1 : ∑ a, w a = 1) (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) :
    gaussianMixtureMeasure w m N = gaussianCodebookKernel m N ∘ₘ finiteWeightLaw w hw hw1 := by
  rw [gaussianCodebookKernel_comp_eq_mixture]
  simp only [finiteWeightLaw_real_singleton]

theorem entropyWith_gaussianCodebook_ge_noise (μ : Measure α) [IsProbabilityMeasure μ]
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef) :
    entropyWith (multivariateGaussian 0 N) volume ≤
      entropyWith (gaussianCodebookKernel m N ∘ₘ μ) volume := by
  have he := mutualInfo_gaussianMixture_eq_entropy_sub μ (gaussianCodebookKernel m N) m N hN
    (fun _ ↦ rfl)
  have hpos := ENNReal.toReal_nonneg (a := mutualInfo (μ ⊗ₘ gaussianCodebookKernel m N))
  linarith

theorem integral_quadratic_gaussianCodebook (μ : Measure α) [IsProbabilityMeasure μ]
    (m : α → EuclideanSpace ℝ ι) (N A : Matrix ι ι ℝ) (hN : N.PosSemidef) :
    (∫ y : EuclideanSpace ℝ ι, y ⬝ᵥ A *ᵥ y ∂gaussianCodebookKernel m N ∘ₘ μ) =
      trace (A * N) + ∫ a, m a ⬝ᵥ A *ᵥ m a ∂μ := by
  have hi : Integrable (fun y : EuclideanSpace ℝ ι ↦ y ⬝ᵥ A *ᵥ y)
      (gaussianCodebookKernel m N ∘ₘ μ) := by
    simpa only [sub_zero, WithLp.ofLp_zero] using integrable_covarianceQuadratic
      (memLp_eval_gaussianMixture μ (gaussianCodebookKernel m N) m N (fun _ ↦ rfl)) 0 A
  rw [integral_comp_eq_integral μ _ hi]
  have he (a : α) : (∫ y : EuclideanSpace ℝ ι, y ⬝ᵥ A *ᵥ y ∂gaussianCodebookKernel m N a) =
      trace (A * N) + m a ⬝ᵥ A *ᵥ m a := by
    simpa only [gaussianCodebookKernel_apply, sub_zero, WithLp.ofLp_zero] using
      integral_quadratic_multivariateGaussian (m a) 0 N A hN
  simp_rw [he]
  rw [integral_add (integrable_const _) Integrable.of_finite]
  simp only [integral_const, probReal_univ, one_smul]

theorem entropyWith_gaussianCodebook_le_reference (μ : Measure α) [IsProbabilityMeasure μ]
    (m : α → EuclideanSpace ℝ ι) (N T : Matrix ι ι ℝ) (hN : N.PosDef) (hT : T.PosDef) :
    entropyWith (gaussianCodebookKernel m N ∘ₘ μ) volume ≤
      entropyWith (multivariateGaussian 0 T) volume +
        (trace (T⁻¹ * N) + (∫ a, m a ⬝ᵥ T⁻¹ *ᵥ m a ∂μ) - Fintype.card ι) / 2 := by
  have h := entropyWith_le_multivariateGaussian_crossEntropy
    (gaussianCodebookKernel_output_ac μ m N hN)
    (gaussianCodebookKernel_output_integrable_llr μ m N hN) 0 T hT
    (integrable_covarianceQuadratic
      (memLp_eval_gaussianMixture μ (gaussianCodebookKernel m N) m N (fun _ ↦ rfl)) 0 T⁻¹)
  simp only [sub_zero, WithLp.ofLp_zero] at h
  rw [integral_quadratic_gaussianCodebook μ m N T⁻¹ hN.posSemidef] at h
  rw [entropyWith_multivariateGaussian 0 T hT]
  linarith

end MeasurableLabels

theorem entropyWith_gaussianMixtureMeasure_ge_noise (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hw1 : ∑ a, w a = 1) (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef) :
    entropyWith (multivariateGaussian 0 N) volume ≤ entropyWith (gaussianMixtureMeasure w m N) volume := by
  letI : MeasurableSpace α := ⊤
  rw [gaussianMixtureMeasure_eq_codebook w hw hw1 m N]
  exact entropyWith_gaussianCodebook_ge_noise _ m N hN

theorem entropyWith_gaussianMixtureMeasure_le_reference (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hw1 : ∑ a, w a = 1) (m : α → EuclideanSpace ℝ ι) (N T : Matrix ι ι ℝ)
    (hN : N.PosDef) (hT : T.PosDef) :
    entropyWith (gaussianMixtureMeasure w m N) volume ≤
      entropyWith (multivariateGaussian 0 T) volume +
        (trace (T⁻¹ * N) + (∑ a, w a * (m a ⬝ᵥ T⁻¹ *ᵥ m a)) - Fintype.card ι) / 2 := by
  letI : MeasurableSpace α := ⊤
  rw [gaussianMixtureMeasure_eq_codebook w hw hw1 m N]
  have h := entropyWith_gaussianCodebook_le_reference (finiteWeightLaw w hw hw1) m N T hN hT
  simpa only [integral_fintype Integrable.of_finite, finiteWeightLaw_real_singleton, smul_eq_mul] using h

theorem entropyWith_gaussianMixtureMeasure_le_noise_add (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hw1 : ∑ a, w a = 1) (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef) :
    entropyWith (gaussianMixtureMeasure w m N) volume ≤
      entropyWith (multivariateGaussian 0 N) volume + (∑ a, w a * (m a ⬝ᵥ N⁻¹ *ᵥ m a)) / 2 := by
  have h := entropyWith_gaussianMixtureMeasure_le_reference w hw hw1 m N N hN hN
  simpa only [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hN.det_pos.ne'), trace_one,
    add_sub_cancel_left] using h

end CapacityAtlas.MeasureInformation
