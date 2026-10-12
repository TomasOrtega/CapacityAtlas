/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.MultivariateGaussianEntropy
import CapacityAtlasForMathlib.InformationTheory.ConditionalDifferentialEntropy
import CapacityAtlasForMathlib.Probability.GaussianChannel

open MeasureTheory ProbabilityTheory Real Matrix
open scoped BigOperators

namespace CapacityAtlas.MeasureInformation

variable {ι ο : Type*} [Fintype ι] [Fintype ο] [DecidableEq ι] [DecidableEq ο]

lemma gaussianChannel_density_physical (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (x : EuclideanSpace ℝ ι) (z : EuclideanSpace ℝ ο) :
    multivariateGaussianPDFReal (H.toEuclideanLin x) N (H.toEuclideanLin x + z) =
      multivariateGaussianPDFReal 0 N z := by
  simp only [multivariateGaussianPDFReal, WithLp.ofLp_add, WithLp.ofLp_zero,
    add_sub_cancel_left, sub_zero]

lemma integrable_log_gaussianChannel_density (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (hN : N.PosDef) (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ] :
    Integrable (fun p ↦ log (multivariateGaussianPDFReal (H.toEuclideanLin p.1) N p.2))
      (μ ⊗ₘ gaussianChannel H N) := by
  rw [gaussianChannel_compProd_eq_map]
  apply (integrable_map_measure
    (measurable_gaussianChannel_density H N).log.aestronglyMeasurable (by fun_prop)).mpr
  have hnoise := integrable_log_multivariateGaussianPDFReal 0 N hN
    (integrable_covarianceQuadratic_multivariateGaussian 0 N hN)
  simpa only [Function.comp_def, gaussianChannel_density_physical] using hnoise.comp_snd μ

theorem integrable_llr_gaussianChannel_compProd (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (hN : N.PosDef) (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ] :
    Integrable (llr (μ ⊗ₘ gaussianChannel H N) (μ.prod volume))
      (μ ⊗ₘ gaussianChannel H N) := by
  apply (integrable_log_gaussianChannel_density H N hN μ).congr
  exact (llr_gaussianChannel_compProd H N hN μ).symm

lemma integral_log_gaussianChannel_density (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    (∫ p, log (multivariateGaussianPDFReal (H.toEuclideanLin p.1) N p.2)
      ∂(μ ⊗ₘ gaussianChannel H N)) =
      ∫ z, log (multivariateGaussianPDFReal 0 N z) ∂multivariateGaussian 0 N := by
  rw [gaussianChannel_compProd_eq_map, integral_map (by fun_prop)
    (measurable_gaussianChannel_density H N).log.aestronglyMeasurable]
  simp_rw [gaussianChannel_density_physical]
  simpa only [probReal_univ, one_smul] using
    (integral_fun_snd (μ := μ) (ν := multivariateGaussian 0 N)
      (fun z ↦ log (multivariateGaussianPDFReal 0 N z)))

theorem entropyWith_gaussianChannel_compProd (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (hN : N.PosDef) (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    entropyWith (μ ⊗ₘ gaussianChannel H N) (μ.prod volume) =
      entropyWith (multivariateGaussian 0 N) volume := by
  rw [entropyWith, entropyWith,
    integral_congr_ae (llr_gaussianChannel_compProd H N hN μ),
    integral_congr_ae (llr_multivariateGaussian_volume 0 N hN),
    integral_log_gaussianChannel_density]

theorem mutualInfo_gaussianChannel_ne_top (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (hN : N.PosDef) (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hout : Integrable (llr (gaussianChannel H N ∘ₘ μ) volume) (gaussianChannel H N ∘ₘ μ)) :
    mutualInfo (μ ⊗ₘ gaussianChannel H N) ≠ ⊤ := by
  apply mutualInfo_ne_top_of_integrable_log_density _ volume
  · simpa only [Measure.fst_compProd] using
      gaussianChannel_compProd_absolutelyContinuous H N hN μ
  · simpa only [Measure.fst_compProd] using integrable_llr_gaussianChannel_compProd H N hN μ
  · simpa only [Measure.snd_compProd] using hout

theorem mutualInfo_gaussianChannel_eq_entropy_sub (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (hN : N.PosDef) (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hout : Integrable (llr (gaussianChannel H N ∘ₘ μ) volume) (gaussianChannel H N ∘ₘ μ)) :
    (mutualInfo (μ ⊗ₘ gaussianChannel H N)).toReal =
      entropyWith (gaussianChannel H N ∘ₘ μ) volume -
        entropyWith (multivariateGaussian 0 N) volume := by
  have h := mutualInfo_eq_entropy_sub_joint (μ ⊗ₘ gaussianChannel H N) volume
    (by simpa only [Measure.fst_compProd] using
      gaussianChannel_compProd_absolutelyContinuous H N hN μ)
    (by simpa only [Measure.fst_compProd] using integrable_llr_gaussianChannel_compProd H N hN μ)
    (by simpa only [Measure.snd_compProd] using hout)
  simpa only [Measure.fst_compProd, Measure.snd_compProd,
    entropyWith_gaussianChannel_compProd H N hN μ] using h

theorem integrable_llr_gaussianChannel_output (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (hN : N.PosDef) (m : EuclideanSpace ℝ ι) (Q : Matrix ι ι ℝ) (hQ : Q.PosSemidef) :
    Integrable (llr (gaussianChannel H N ∘ₘ multivariateGaussian m Q) volume)
      (gaussianChannel H N ∘ₘ multivariateGaussian m Q) := by
  rw [gaussianChannel_comp_multivariateGaussian H N hN.posSemidef m Q hQ]
  exact integrable_llr_multivariateGaussian_volume _ _
    (gaussianChannel_output_covariance_posDef H N hN Q hQ)

theorem mutualInfo_gaussianChannel_gaussian_ne_top (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (hN : N.PosDef) (m : EuclideanSpace ℝ ι) (Q : Matrix ι ι ℝ) (hQ : Q.PosSemidef) :
    mutualInfo (multivariateGaussian m Q ⊗ₘ gaussianChannel H N) ≠ ⊤ :=
  mutualInfo_gaussianChannel_ne_top H N hN _ (integrable_llr_gaussianChannel_output H N hN m Q hQ)

theorem mutualInfo_gaussianChannel_gaussian (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (hN : N.PosDef) (m : EuclideanSpace ℝ ι) (Q : Matrix ι ι ℝ) (hQ : Q.PosSemidef) :
    (mutualInfo (multivariateGaussian m Q ⊗ₘ gaussianChannel H N)).toReal =
      (log (N + H * Q * H.transpose).det - log N.det) / 2 := by
  rw [mutualInfo_gaussianChannel_eq_entropy_sub H N hN _
    (integrable_llr_gaussianChannel_output H N hN m Q hQ),
    gaussianChannel_comp_multivariateGaussian H N hN.posSemidef m Q hQ,
    entropyWith_multivariateGaussian _ _ (gaussianChannel_output_covariance_posDef H N hN Q hQ),
    entropyWith_multivariateGaussian _ _ hN]
  ring

theorem mutualInfo_gaussianChannel_gaussian_eq_log_det_ratio
    (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ) (hN : N.PosDef)
    (m : EuclideanSpace ℝ ι) (Q : Matrix ι ι ℝ) (hQ : Q.PosSemidef) :
    (mutualInfo (multivariateGaussian m Q ⊗ₘ gaussianChannel H N)).toReal =
      log ((N + H * Q * H.transpose).det / N.det) / 2 := by
  rw [mutualInfo_gaussianChannel_gaussian H N hN m Q hQ,
    log_div (gaussianChannel_output_covariance_posDef H N hN Q hQ).det_pos.ne' hN.det_pos.ne']

theorem mutualInfo_gaussianChannel_gaussian_eq
    (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ) (hN : N.PosDef)
    (m : EuclideanSpace ℝ ι) (Q : Matrix ι ι ℝ) (hQ : Q.PosSemidef) :
    mutualInfo (multivariateGaussian m Q ⊗ₘ gaussianChannel H N) =
      ENNReal.ofReal (log ((N + H * Q * H.transpose).det / N.det) / 2) := by
  rw [← mutualInfo_gaussianChannel_gaussian_eq_log_det_ratio H N hN m Q hQ,
    ENNReal.ofReal_toReal (mutualInfo_gaussianChannel_gaussian_ne_top H N hN m Q hQ)]

end CapacityAtlas.MeasureInformation
