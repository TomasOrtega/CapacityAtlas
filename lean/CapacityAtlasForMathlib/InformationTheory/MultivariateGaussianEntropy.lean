/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianEntropy
import CapacityAtlasForMathlib.Probability.GaussianDensity
import CapacityAtlasForMathlib.Probability.VectorCovariance

open MeasureTheory ProbabilityTheory Real Matrix
open scoped BigOperators NNReal MatrixOrder

namespace CapacityAtlas.MeasureInformation

variable {ι : Type*} [Fintype ι]

lemma integral_norm_sq_stdGaussian :
    ∫ x : EuclideanSpace ℝ ι, ‖x‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) = Fintype.card ι := by
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  change (∫ x : ι → ℝ, ∑ i, (x i) ^ 2 ∂Measure.pi (fun _ ↦ gaussianReal 0 1)) = _
  rw [integral_finsetSum]
  · simp_rw [integral_comp_eval (μ := fun _ : ι ↦ gaussianReal 0 1)
      (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)]
    have hi := integral_centered_sq_gaussianReal 0 1
    simp only [sub_zero, NNReal.coe_one] at hi
    simp [hi]
  · intro i _
    simpa using integrable_comp_eval (μ := fun _ : ι ↦ gaussianReal 0 1) (i := i)
      ((memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq)

lemma log_stdGaussian_density (x : EuclideanSpace ℝ ι) :
    log (∏ i, gaussianPDFReal 0 1 (x i)) =
      -(Fintype.card ι : ℝ) * log (2 * π) / 2 - ‖x‖ ^ 2 / 2 := by
  rw [prod_gaussianPDFReal_zero_one,
    log_mul (pow_ne_zero _ (inv_ne_zero (sqrt_pos.mpr (by positivity)).ne')) (exp_pos _).ne',
    log_pow, log_inv, log_sqrt (by positivity), log_exp]
  ring

lemma llr_stdGaussian_volume :
    llr (stdGaussian (EuclideanSpace ℝ ι)) volume =ᵐ[stdGaussian (EuclideanSpace ℝ ι)]
      fun x ↦ -(Fintype.card ι : ℝ) * log (2 * π) / 2 - ‖x‖ ^ 2 / 2 := by
  have hac : stdGaussian (EuclideanSpace ℝ ι) ≪ volume := by
    rw [stdGaussian_eq_withDensity_prod]
    exact withDensity_absolutelyContinuous _ _
  have hrn := Measure.rnDeriv_withDensity (volume : Measure (EuclideanSpace ℝ ι))
    (show Measurable (fun x : EuclideanSpace ℝ ι ↦
      ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) by fun_prop)
  rw [← stdGaussian_eq_withDensity_prod] at hrn
  filter_upwards [hac.ae_le hrn] with x hx
  rw [llr, hx, ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ ↦ gaussianPDFReal_nonneg _ _ _)]
  exact log_stdGaussian_density x

lemma integrable_llr_stdGaussian_volume :
    Integrable (llr (stdGaussian (EuclideanSpace ℝ ι)) volume)
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  have hnorm : Integrable (fun x : EuclideanSpace ℝ ι ↦ ‖x‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ ι)) :=
    (IsGaussian.memLp_two_id (μ := stdGaussian (EuclideanSpace ℝ ι))).integrable_norm_pow'
  apply ((integrable_const _).sub (hnorm.div_const 2)).congr
  filter_upwards [llr_stdGaussian_volume (ι := ι)] with x hx using hx.symm

theorem entropyWith_stdGaussian :
    entropyWith (stdGaussian (EuclideanSpace ℝ ι)) volume =
      Fintype.card ι * (log (2 * π) + 1) / 2 := by
  have hnorm : Integrable (fun x : EuclideanSpace ℝ ι ↦ ‖x‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ ι)) :=
    (IsGaussian.memLp_two_id (μ := stdGaussian (EuclideanSpace ℝ ι))).integrable_norm_pow'
  rw [entropyWith, integral_congr_ae llr_stdGaussian_volume,
    integral_sub (integrable_const _) (hnorm.div_const 2)]
  simp_rw [integral_div]
  rw [integral_norm_sq_stdGaussian]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

variable [DecidableEq ι]

lemma covarianceQuadratic_sqrt (S : Matrix ι ι ℝ) (hS : S.PosDef)
    (x : EuclideanSpace ℝ ι) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x) ⬝ᵥ S⁻¹ *ᵥ
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x) = ‖x‖ ^ 2 := by
  rw [← norm_inv_covarianceSqrt_sq S hS, ← covarianceSqrtEquiv_symm_apply S hS,
    ← covarianceSqrtEquiv_apply S hS, ContinuousLinearEquiv.symm_apply_apply]

lemma covarianceQuadratic_affine_stdGaussian (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) (hS : S.PosDef) (x : EuclideanSpace ℝ ι) :
    ((m + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x) - m) ⬝ᵥ S⁻¹ *ᵥ
      ((m + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x) - m) = ‖x‖ ^ 2 := by
  simp only [add_sub_cancel_left]
  exact covarianceQuadratic_sqrt S hS x

lemma integrable_covarianceQuadratic_multivariateGaussian (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) (hS : S.PosDef) :
    Integrable (fun x : EuclideanSpace ℝ ι ↦ (x - m) ⬝ᵥ S⁻¹ *ᵥ (x - m))
      (multivariateGaussian m S) := by
  rw [multivariateGaussian]
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  simpa only [Function.comp_def, WithLp.ofLp_sub, WithLp.ofLp_add, add_sub_cancel_left,
    covarianceQuadratic_sqrt S hS, id_eq] using
    (IsGaussian.memLp_two_id (μ := stdGaussian (EuclideanSpace ℝ ι))).integrable_norm_pow'

lemma integral_covarianceQuadratic_multivariateGaussian (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) (hS : S.PosDef) :
    (∫ x : EuclideanSpace ℝ ι, (x - m) ⬝ᵥ S⁻¹ *ᵥ (x - m)
      ∂multivariateGaussian m S) = Fintype.card ι := by
  rw [multivariateGaussian, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [WithLp.ofLp_sub, WithLp.ofLp_add, add_sub_cancel_left, covarianceQuadratic_sqrt S hS]
  exact integral_norm_sq_stdGaussian

lemma integrable_llr_multivariateGaussian_volume (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) (hS : S.PosDef) :
    Integrable (llr (multivariateGaussian m S) volume) (multivariateGaussian m S) := by
  apply (integrable_log_multivariateGaussianPDFReal m S hS
    (integrable_covarianceQuadratic_multivariateGaussian m S hS)).congr
  filter_upwards [llr_multivariateGaussian_volume m S hS] with x hx using hx.symm

/-- Differential entropy of the native nondegenerate vector Gaussian, in nats. -/
theorem entropyWith_multivariateGaussian (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) (hS : S.PosDef) :
    entropyWith (multivariateGaussian m S) volume =
      (Fintype.card ι * (log (2 * π) + 1) + log S.det) / 2 := by
  rw [entropyWith, integral_congr_ae (llr_multivariateGaussian_volume m S hS),
    integral_log_multivariateGaussianPDFReal m S hS
      (integrable_covarianceQuadratic_multivariateGaussian m S hS),
    integral_covarianceQuadratic_multivariateGaussian m S hS]
  ring

theorem entropyWith_le_multivariateGaussian_crossEntropy
    {μ : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (hlog : Integrable (llr μ volume) μ)
    (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (hS : S.PosDef)
    (hquad : Integrable (fun x : EuclideanSpace ℝ ι ↦ (x - m) ⬝ᵥ S⁻¹ *ᵥ (x - m)) μ) :
    entropyWith μ volume ≤
      (Fintype.card ι * log (2 * π) + log S.det) / 2 +
        (∫ x, (x - m) ⬝ᵥ S⁻¹ *ᵥ (x - m) ∂μ) / 2 := by
  have hexp : Integrable (fun x ↦ exp (log (multivariateGaussianPDFReal m S x))) volume := by
    simpa only [exp_log (multivariateGaussianPDFReal_pos m S hS _)] using
      integrable_multivariateGaussianPDFReal m S hS
  have h := entropyWith_le_log_partition_sub_integral hμ
    (integrable_log_multivariateGaussianPDFReal m S hS hquad) hexp hlog
  simp_rw [exp_log (multivariateGaussianPDFReal_pos m S hS _)] at h
  rw [integral_multivariateGaussianPDFReal m S hS, log_one,
    integral_log_multivariateGaussianPDFReal m S hS hquad] at h
  linarith

theorem entropyWith_le_multivariateGaussian
    {μ : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (hlog : Integrable (llr μ volume) μ)
    (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (hS : S.PosDef)
    (hquad : Integrable (fun x : EuclideanSpace ℝ ι ↦ (x - m) ⬝ᵥ S⁻¹ *ᵥ (x - m)) μ)
    (hmoment : (∫ x, (x - m) ⬝ᵥ S⁻¹ *ᵥ (x - m) ∂μ) ≤ Fintype.card ι) :
    entropyWith μ volume ≤ entropyWith (multivariateGaussian m S) volume := by
  rw [entropyWith_multivariateGaussian m S hS]
  have h := entropyWith_le_multivariateGaussian_crossEntropy hμ hlog m S hS hquad
  linarith

theorem klDiv_multivariateGaussian_eq_crossEntropy_sub_entropy
    {μ : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (hlog : Integrable (llr μ volume) μ)
    (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (hS : S.PosDef)
    (hquad : Integrable (fun x : EuclideanSpace ℝ ι ↦ (x - m) ⬝ᵥ S⁻¹ *ᵥ (x - m)) μ) :
    (_root_.InformationTheory.klDiv μ (multivariateGaussian m S)).toReal =
      (Fintype.card ι * log (2 * π) + log S.det) / 2 +
        (∫ x, (x - m) ⬝ᵥ S⁻¹ *ᵥ (x - m) ∂μ) / 2 - entropyWith μ volume := by
  have hexp : Integrable (fun x ↦ exp (log (multivariateGaussianPDFReal m S x))) volume := by
    simpa only [exp_log (multivariateGaussianPDFReal_pos m S hS _)] using
      integrable_multivariateGaussianPDFReal m S hS
  rw [multivariateGaussian_eq_tilted_log_density m S hS,
    klDiv_tilted_eq_entropy_gap hμ
      (integrable_log_multivariateGaussianPDFReal m S hS hquad) hexp hlog]
  simp_rw [exp_log (multivariateGaussianPDFReal_pos m S hS _)]
  rw [integral_multivariateGaussianPDFReal m S hS, log_one,
    integral_log_multivariateGaussianPDFReal m S hS hquad]
  ring

/-- With the same quadratic moment, only the Gaussian attains the entropy bound. -/
theorem entropyWith_eq_multivariateGaussian_iff
    {μ : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (hlog : Integrable (llr μ volume) μ)
    (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (hS : S.PosDef)
    (hquad : Integrable (fun x : EuclideanSpace ℝ ι ↦ (x - m) ⬝ᵥ S⁻¹ *ᵥ (x - m)) μ)
    (hmoment : (∫ x, (x - m) ⬝ᵥ S⁻¹ *ᵥ (x - m) ∂μ) = Fintype.card ι) :
    entropyWith μ volume = entropyWith (multivariateGaussian m S) volume ↔
      μ = multivariateGaussian m S := by
  have hexp : Integrable (fun x ↦ exp (log (multivariateGaussianPDFReal m S x))) volume := by
    simpa only [exp_log (multivariateGaussianPDFReal_pos m S hS _)] using
      integrable_multivariateGaussianPDFReal m S hS
  have h := entropyWith_eq_log_partition_sub_integral_iff hμ
    (integrable_log_multivariateGaussianPDFReal m S hS hquad) hexp hlog
  simp_rw [exp_log (multivariateGaussianPDFReal_pos m S hS _)] at h
  rw [integral_multivariateGaussianPDFReal m S hS, log_one,
    integral_log_multivariateGaussianPDFReal m S hS hquad, hmoment,
    ← multivariateGaussian_eq_tilted_log_density m S hS] at h
  rw [entropyWith_multivariateGaussian m S hS]
  convert h using 2
  ring

/-- Gaussian maximum entropy under the actual coordinate mean and covariance constraints. -/
theorem entropyWith_le_multivariateGaussian_of_covariance
    {μ : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (hlog : Integrable (llr μ volume) μ)
    (hL2 : ∀ i, MemLp (fun x : EuclideanSpace ℝ ι ↦ x i) 2 μ)
    (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (hS : S.PosDef)
    (hm : ∀ i, (∫ x : EuclideanSpace ℝ ι, x i ∂μ) = m i)
    (hcov : ∀ i j, covariance (fun x : EuclideanSpace ℝ ι ↦ x i) (fun x ↦ x j) μ = S i j) :
    entropyWith μ volume ≤ entropyWith (multivariateGaussian m S) volume :=
  entropyWith_le_multivariateGaussian hμ hlog m S hS
    (integrable_covarianceQuadratic hL2 m S⁻¹)
    (integral_inv_covarianceQuadratic hL2 m S hS hm hcov).le

theorem entropyWith_eq_multivariateGaussian_iff_of_covariance
    {μ : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (hlog : Integrable (llr μ volume) μ)
    (hL2 : ∀ i, MemLp (fun x : EuclideanSpace ℝ ι ↦ x i) 2 μ)
    (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (hS : S.PosDef)
    (hm : ∀ i, (∫ x : EuclideanSpace ℝ ι, x i ∂μ) = m i)
    (hcov : ∀ i j, covariance (fun x : EuclideanSpace ℝ ι ↦ x i) (fun x ↦ x j) μ = S i j) :
    entropyWith μ volume = entropyWith (multivariateGaussian m S) volume ↔
      μ = multivariateGaussian m S :=
  entropyWith_eq_multivariateGaussian_iff hμ hlog m S hS
    (integrable_covarianceQuadratic hL2 m S⁻¹)
    (integral_inv_covarianceQuadratic hL2 m S hS hm hcov)

end CapacityAtlas.MeasureInformation
