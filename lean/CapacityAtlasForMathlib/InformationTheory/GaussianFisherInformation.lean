/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FisherInformation
import CapacityAtlasForMathlib.InformationTheory.GaussianRelativeEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MeasureTheory ProbabilityTheory Real Matrix
open scoped BigOperators

namespace CapacityAtlas.MeasureInformation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma quadratic_add_smul (A : Matrix ι ι ℝ) (hA : A.IsSymm) (x v : ι → ℝ) (t : ℝ) :
    (x + t • v) ⬝ᵥ A *ᵥ (x + t • v) =
      x ⬝ᵥ A *ᵥ x + t * (2 * (v ⬝ᵥ A *ᵥ x)) + t ^ 2 * (v ⬝ᵥ A *ᵥ v) := by
  have hcross : x ⬝ᵥ A *ᵥ v = v ⬝ᵥ A *ᵥ x := by
    simpa only [hA.eq] using Matrix.dotProduct_transpose_mulVec A x v
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [hcross]
  ring

omit [DecidableEq ι] in
lemma hasLineDerivAt_covarianceQuadratic (m x v : EuclideanSpace ℝ ι)
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) :
    HasLineDerivAt ℝ (fun y : EuclideanSpace ℝ ι ↦ (y - m) ⬝ᵥ A *ᵥ (y - m))
      (2 * (v ⬝ᵥ A *ᵥ (x - m))) x v := by
  have heq (t : ℝ) : (x + t • v - m) ⬝ᵥ A *ᵥ (x + t • v - m) =
      (x - m) ⬝ᵥ A *ᵥ (x - m) + t * (2 * (v ⬝ᵥ A *ᵥ (x - m))) +
        t ^ 2 * (v ⬝ᵥ A *ᵥ v) := by
    simp only [WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul]
    have hshift : x.ofLp + t • v.ofLp - m.ofLp = (x.ofLp - m.ofLp) + t • v.ofLp := by module
    rw [hshift]
    exact quadratic_add_smul A hA _ _ t
  unfold HasLineDerivAt
  change HasDerivAt (fun t : ℝ ↦ (x + t • v - m) ⬝ᵥ A *ᵥ (x + t • v - m))
    (2 * (v ⬝ᵥ A *ᵥ (x - m))) 0
  simp_rw [heq]
  convert! ((hasDerivAt_const (0 : ℝ) ((x - m) ⬝ᵥ A *ᵥ (x - m))).add
    ((hasDerivAt_id 0).mul_const (2 * (v ⬝ᵥ A *ᵥ (x - m))))).add
      (((hasDerivAt_id 0).pow 2).mul_const (v ⬝ᵥ A *ᵥ v)) using 1
  simp

/-- The native Gaussian log density has the inverse-covariance directional score. -/
theorem hasLineDerivAt_log_multivariateGaussianPDFReal
    (m x v : EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef) :
    HasLineDerivAt ℝ (fun y ↦ log (multivariateGaussianPDFReal m N y))
      (-(v ⬝ᵥ N⁻¹ *ᵥ (x - m))) x v := by
  have hquad := hasLineDerivAt_covarianceQuadratic m x v N⁻¹
    (isHermitian_iff_isSymm.mp hN.inv.isHermitian)
  unfold HasLineDerivAt at hquad ⊢
  simp_rw [log_multivariateGaussianPDFReal m N hN]
  convert! (hasDerivAt_const (0 : ℝ)
    (-((Fintype.card ι : ℝ) * log (2 * π) + log N.det) / 2)).sub (hquad.div_const 2) using 1
  ring

theorem hasLineDerivAt_multivariateGaussianPDFReal
    (m x v : EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef) :
    HasLineDerivAt ℝ (multivariateGaussianPDFReal m N)
      (-(v ⬝ᵥ N⁻¹ *ᵥ (x - m)) * multivariateGaussianPDFReal m N x) x v := by
  have h := (hasLineDerivAt_log_multivariateGaussianPDFReal m x v N hN).exp
  simpa only [HasLineDerivAt, exp_log (multivariateGaussianPDFReal_pos m N hN _),
    zero_smul, add_zero, mul_comm] using h

omit [DecidableEq ι] in
lemma hasLineDerivAt_dotProduct_sub (m x v : EuclideanSpace ℝ ι) (w : ι → ℝ) :
    HasLineDerivAt ℝ (fun y : EuclideanSpace ℝ ι ↦ w ⬝ᵥ (y - m)) (w ⬝ᵥ v) x v := by
  have heq (t : ℝ) : w ⬝ᵥ (x + t • v - m) = w ⬝ᵥ (x - m) + t * (w ⬝ᵥ v) := by
    simp only [dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]
    ring
  unfold HasLineDerivAt
  change HasDerivAt (fun t : ℝ ↦ w ⬝ᵥ (x + t • v - m)) (w ⬝ᵥ v) 0
  simp_rw [heq]
  convert! (hasDerivAt_const (0 : ℝ) (w ⬝ᵥ (x - m))).add
    ((hasDerivAt_id 0).mul_const (w ⬝ᵥ v))
    using 1
  simp

/-- The second directional derivative of a native Gaussian density. -/
theorem hasLineDerivAt_lineDeriv_multivariateGaussianPDFReal
    (m x v : EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef) :
    HasLineDerivAt ℝ (fun y ↦ lineDeriv ℝ (multivariateGaussianPDFReal m N) y v)
      (((v ⬝ᵥ N⁻¹ *ᵥ (x - m)) ^ 2 - v ⬝ᵥ N⁻¹ *ᵥ v) *
        multivariateGaussianPDFReal m N x) x v := by
  have hscore : HasLineDerivAt ℝ
      (fun y : EuclideanSpace ℝ ι ↦ v ⬝ᵥ N⁻¹ *ᵥ (y - m))
      (v ⬝ᵥ N⁻¹ *ᵥ v) x v := by
    simpa only [Matrix.dotProduct_mulVec] using
      hasLineDerivAt_dotProduct_sub m x v (v ᵥ* N⁻¹)
  simp_rw [(hasLineDerivAt_multivariateGaussianPDFReal m _ v N hN).lineDeriv]
  unfold HasLineDerivAt at hscore ⊢
  convert! hscore.neg.mul (hasLineDerivAt_multivariateGaussianPDFReal m x v N hN) using 1
  simp only [Pi.neg_apply, zero_smul, add_zero]
  ring

omit [DecidableEq ι] in
lemma quadratic_vecMulVec (w z : ι → ℝ) :
    z ⬝ᵥ (Matrix.vecMulVec w w) *ᵥ z = (w ⬝ᵥ z) ^ 2 := by
  rw [Matrix.vecMulVec_mulVec]
  simp only [op_smul_eq_smul, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm z w, pow_two]

lemma integral_sq_dotProduct_sub_multivariateGaussian
    (m : EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosSemidef) (w : ι → ℝ) :
    (∫ x : EuclideanSpace ℝ ι, (w ⬝ᵥ (x - m)) ^ 2 ∂multivariateGaussian m N) =
      w ⬝ᵥ N *ᵥ w := by
  have h := integral_quadratic_multivariateGaussian m m N (Matrix.vecMulVec w w) hN
  simp only [WithLp.ofLp_sub, WithLp.ofLp_zero, quadratic_vecMulVec, sub_self,
    Matrix.mulVec_zero, dotProduct_zero, add_zero,
    Matrix.vecMulVec_mul, Matrix.trace_vecMulVec] at h
  rw [h, ← Matrix.mulVec_transpose, (isHermitian_iff_isSymm.mp hN.isHermitian).eq]

lemma gaussian_fisher_integrand (m x v : EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) :
    (lineDeriv ℝ (multivariateGaussianPDFReal m N) x v) ^ 2 /
      multivariateGaussianPDFReal m N x =
      multivariateGaussianPDFReal m N x * (v ⬝ᵥ N⁻¹ *ᵥ (x - m)) ^ 2 := by
  rw [(hasLineDerivAt_multivariateGaussianPDFReal m x v N hN).lineDeriv]
  field_simp [(multivariateGaussianPDFReal_pos m N hN x).ne']

/-- The native Gaussian's Fisher information is its inverse covariance in each direction. -/
theorem directionalFisherWith_multivariateGaussian
    (m v : EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef) :
    directionalFisherWith volume (multivariateGaussianPDFReal m N) v = v ⬝ᵥ N⁻¹ *ᵥ v := by
  have hmeasure := integral_withDensity_eq_integral_toReal_smul (μ := volume)
    (measurable_multivariateGaussianPDFReal m N).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))
    (fun x : EuclideanSpace ℝ ι ↦ (v ⬝ᵥ N⁻¹ *ᵥ (x - m)) ^ 2)
  rw [← multivariateGaussian_eq_withDensity m N hN] at hmeasure
  simp only [ENNReal.toReal_ofReal (multivariateGaussianPDFReal_pos m N hN _).le,
    smul_eq_mul] at hmeasure
  rw [directionalFisherWith]
  simp_rw [gaussian_fisher_integrand m _ v N hN]
  rw [← hmeasure]
  simp_rw [Matrix.dotProduct_mulVec]
  rw [integral_sq_dotProduct_sub_multivariateGaussian m N hN.posSemidef]
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul N (isUnit_iff_ne_zero.mpr hN.det_pos.ne'), Matrix.one_mulVec,
    dotProduct_comm]

lemma integrable_multivariateGaussianPDFReal_mul_iff (m : EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) (f : EuclideanSpace ℝ ι → ℝ) :
    Integrable (fun x ↦ multivariateGaussianPDFReal m N x * f x) volume ↔
      Integrable f (multivariateGaussian m N) := by
  rw [multivariateGaussian_eq_withDensity m N hN,
    integrable_withDensity_iff_integrable_smul'
      (measurable_multivariateGaussianPDFReal m N).ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (multivariateGaussianPDFReal_pos m N hN _).le,
    smul_eq_mul]

lemma integrable_sq_dotProduct_sub_multivariateGaussian
    (m : EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (w : ι → ℝ) :
    Integrable (fun x : EuclideanSpace ℝ ι ↦ (w ⬝ᵥ (x - m)) ^ 2)
      (multivariateGaussian m N) := by
  have h := integrable_covarianceQuadratic (memLp_eval_multivariateGaussian m N)
    m (Matrix.vecMulVec w w)
  simpa only [WithLp.ofLp_sub, quadratic_vecMulVec] using h

lemma integrable_gaussian_fisher_integrand (m v : EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) :
    Integrable (fun x ↦ (lineDeriv ℝ (multivariateGaussianPDFReal m N) x v) ^ 2 /
      multivariateGaussianPDFReal m N x) volume := by
  simp_rw [gaussian_fisher_integrand m _ v N hN]
  apply (integrable_multivariateGaussianPDFReal_mul_iff m N hN _).mpr
  simpa only [Matrix.dotProduct_mulVec] using
    integrable_sq_dotProduct_sub_multivariateGaussian m N (v ᵥ* N⁻¹)

lemma measurable_gaussian_directional_derivative (m v : EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) :
    Measurable (fun x : EuclideanSpace ℝ ι ↦
      -(v ⬝ᵥ N⁻¹ *ᵥ (x - m)) * multivariateGaussianPDFReal m N x) := by
  apply Measurable.mul _ (measurable_multivariateGaussianPDFReal m N)
  simp only [dotProduct, Matrix.mulVec, Pi.sub_apply]
  fun_prop

section FiniteMixture

variable {α : Type*} [Fintype α] (w : α → ℝ) (m : α → EuclideanSpace ℝ ι)
  (N : α → Matrix ι ι ℝ) (hN : ∀ a, (N a).PosDef) (v : EuclideanSpace ℝ ι)

include hN

lemma integrable_fisher_gaussian_mixture (hw : ∀ a, 0 ≤ w a) :
    Integrable (fun x ↦ (lineDeriv ℝ
      (fun y ↦ ∑ a, w a * multivariateGaussianPDFReal (m a) (N a) y) x v) ^ 2 /
      (∑ a, w a * multivariateGaussianPDFReal (m a) (N a) x)) volume := by
  apply integrable_fisher_weighted_sum volume w
    (fun a ↦ multivariateGaussianPDFReal (m a) (N a))
    (fun a x ↦ -(v ⬝ᵥ (N a)⁻¹ *ᵥ (x - m a)) *
      multivariateGaussianPDFReal (m a) (N a) x) v hw
    (fun a ↦ multivariateGaussianPDFReal_pos (m a) (N a) (hN a))
    (fun a ↦ measurable_multivariateGaussianPDFReal (m a) (N a))
    (fun a ↦ measurable_gaussian_directional_derivative (m a) v (N a))
    (fun a x ↦ hasLineDerivAt_multivariateGaussianPDFReal (m a) x v (N a) (hN a))
  intro a
  simpa only [← (hasLineDerivAt_multivariateGaussianPDFReal (m a) _ v
    (N a) (hN a)).lineDeriv] using
      integrable_gaussian_fisher_integrand (m a) v (N a) (hN a)

/-- A native finite Gaussian mixture has at most the average row Fisher information. -/
theorem directionalFisherWith_gaussian_mixture_le (hw : ∀ a, 0 ≤ w a) :
    directionalFisherWith volume
      (fun x ↦ ∑ a, w a * multivariateGaussianPDFReal (m a) (N a) x) v ≤
      ∑ a, w a * (v ⬝ᵥ (N a)⁻¹ *ᵥ v) := by
  calc
    _ ≤ ∑ a, w a * directionalFisherWith volume
        (multivariateGaussianPDFReal (m a) (N a)) v := by
      apply directionalFisherWith_weighted_sum_le volume w
        (fun a ↦ multivariateGaussianPDFReal (m a) (N a))
        (fun a x ↦ -(v ⬝ᵥ (N a)⁻¹ *ᵥ (x - m a)) *
          multivariateGaussianPDFReal (m a) (N a) x) v hw
        (fun a ↦ multivariateGaussianPDFReal_pos (m a) (N a) (hN a))
        (fun a ↦ measurable_multivariateGaussianPDFReal (m a) (N a))
        (fun a ↦ measurable_gaussian_directional_derivative (m a) v (N a))
        (fun a x ↦ hasLineDerivAt_multivariateGaussianPDFReal (m a) x v (N a) (hN a))
      intro a
      simpa only [← (hasLineDerivAt_multivariateGaussianPDFReal (m a) _ v
        (N a) (hN a)).lineDeriv] using
          integrable_gaussian_fisher_integrand (m a) v (N a) (hN a)
    _ = _ := by
      simp only [directionalFisherWith_multivariateGaussian _ _ _ (hN _)]

end FiniteMixture

end CapacityAtlas.MeasureInformation
