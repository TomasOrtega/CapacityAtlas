/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

open MeasureTheory MeasureTheory.Measure Matrix
open scoped BigOperators ENNReal NNReal

namespace MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem map_withDensity_measurableEquiv (μ : Measure α) (e : α ≃ᵐ β)
    (p : α → ℝ≥0∞) (hp : Measurable p) :
    (μ.withDensity p).map e = (μ.map e).withDensity (fun y ↦ p (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs]
  simpa only [Function.comp_apply, e.symm_apply_apply] using
    (setLIntegral_map (μ := μ) hs (hp.comp e.symm.measurable) e.measurable).symm

theorem pi_withDensity_ofReal {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] (μ : (i : ι) → Measure (E i)) [∀ i, SigmaFinite (μ i)]
    (p : (i : ι) → E i → ℝ) (hp : ∀ i, Integrable (p i) (μ i))
    (hnonneg : ∀ i x, 0 ≤ p i x) :
    Measure.pi (fun i ↦ (μ i).withDensity (fun x ↦ ENNReal.ofReal (p i x))) =
      (Measure.pi μ).withDensity (fun x ↦ ENNReal.ofReal (∏ i, p i (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (Integrable.fintype_prod_dep (fun i ↦ (hp i).restrict))
    (Filter.Eventually.of_forall (fun x ↦ Finset.prod_nonneg (fun i _ ↦ hnonneg i (x i)))),
    integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ integral_nonneg (hnonneg i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (hp i).restrict
    (Filter.Eventually.of_forall (hnonneg i))

theorem map_withDensity_continuousLinearEquiv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ] (e : E ≃L[ℝ] E)
    (p : E → ℝ≥0∞) (hp : Measurable p) :
    (μ.withDensity p).map e = μ.withDensity (fun y ↦
      ENNReal.ofReal |(LinearMap.det e.toLinearEquiv.toLinearMap)⁻¹| * p (e.symm y)) := by
  have hmap : μ.map e =
      ENNReal.ofReal |(LinearMap.det e.toLinearEquiv.toLinearMap)⁻¹| • μ :=
    map_linearMap_addHaar_eq_smul_addHaar μ e.toLinearEquiv.isUnit_det'.ne_zero
  change (μ.withDensity p).map e.toHomeomorph.toMeasurableEquiv = _
  rw [map_withDensity_measurableEquiv μ _ p hp]
  change (μ.map e).withDensity (fun y ↦ p (e.symm y)) = _
  rw [hmap, withDensity_smul_measure]
  exact (withDensity_smul (μ := μ) _
    (show Measurable (fun y ↦ p (e.symm y)) from hp.comp e.symm.continuous.measurable)).symm

theorem map_withDensity_const_add {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddLeftInvariant μ]
    (m : E) (p : E → ℝ≥0∞) (hp : Measurable p) :
    (μ.withDensity p).map (fun x ↦ m + x) =
      μ.withDensity (fun y ↦ p (y - m)) := by
  change (μ.withDensity p).map (MeasurableEquiv.addLeft m) = _
  rw [map_withDensity_measurableEquiv μ _ p hp]
  change (μ.map (fun x ↦ m + x)).withDensity (fun y ↦ p (-m + y)) = _
  rw [map_add_left_eq_self]
  congr 1
  ext y
  rw [sub_eq_add_neg, add_comm y (-m)]

end MeasureTheory

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

theorem pi_gaussianReal_zero_one_eq_withDensity :
    Measure.pi (fun _ : ι ↦ gaussianReal 0 1) =
      volume.withDensity (fun x : ι → ℝ ↦ ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
  simp only [gaussianReal_of_var_ne_zero 0 (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  exact pi_withDensity_ofReal (fun _ : ι ↦ volume) (fun _ ↦ gaussianPDFReal 0 1)
    (fun _ ↦ integrable_gaussianPDFReal 0 1) (fun _ ↦ gaussianPDFReal_nonneg 0 1)

theorem stdGaussian_eq_withDensity_prod :
    stdGaussian (EuclideanSpace ℝ ι) = volume.withDensity
      (fun x : EuclideanSpace ℝ ι ↦ ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
  rw [← map_pi_eq_stdGaussian, pi_gaussianReal_zero_one_eq_withDensity]
  have hmeas : Measurable (fun x : ι → ℝ ↦ ENNReal.ofReal
      (∏ i, gaussianPDFReal 0 1 (x i))) := by
    fun_prop
  rw [show WithLp.toLp 2 = ⇑(MeasurableEquiv.toLp 2 (ι → ℝ)) from rfl,
    map_withDensity_measurableEquiv _ _ _ hmeas]
  change ((volume : Measure (ι → ℝ)).map (WithLp.toLp 2)).withDensity _ = _
  rw [(PiLp.volume_preserving_toLp ι).map_eq]
  rfl

theorem prod_gaussianPDFReal_zero_one (x : EuclideanSpace ℝ ι) :
    (∏ i, gaussianPDFReal 0 1 (x i)) =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι * Real.exp (-‖x‖ ^ 2 / 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ← Real.exp_sum, ← Finset.sum_div,
    Finset.sum_neg_distrib, ← EuclideanSpace.real_norm_sq_eq]

open scoped MatrixOrder

variable [DecidableEq ι]

theorem det_toEuclideanCLM (A : Matrix ι ι ℝ) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) A).det = A.det := by
  change LinearMap.det (Matrix.toEuclideanLin A) = _
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]

theorem det_covarianceSqrt_pos {S : Matrix ι ι ℝ} (hS : S.PosDef) :
    0 < (CFC.sqrt S).det := by
  rw [hS.posSemidef.det_sqrt, RCLike.sqrt_of_nonneg hS.det_pos.le]
  exact Real.sqrt_pos.mpr hS.det_pos

/-- The native Gaussian's square-root covariance map as a continuous equivalence. -/
noncomputable def covarianceSqrtEquiv (S : Matrix ι ι ℝ) (hS : S.PosDef) :
    EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)).toContinuousLinearEquivOfDetNeZero
    (by rw [det_toEuclideanCLM]; exact (det_covarianceSqrt_pos hS).ne')

theorem covarianceSqrtEquiv_apply (S : Matrix ι ι ℝ) (hS : S.PosDef)
    (x : EuclideanSpace ℝ ι) :
    covarianceSqrtEquiv S hS x = Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x := rfl

theorem covarianceSqrtEquiv_symm_apply (S : Matrix ι ι ℝ) (hS : S.PosDef)
    (x : EuclideanSpace ℝ ι) :
    (covarianceSqrtEquiv S hS).symm x =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹ x := by
  apply (covarianceSqrtEquiv S hS).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, covarianceSqrtEquiv_apply]
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (det_covarianceSqrt_pos hS).ne'), map_one]
  rfl

theorem det_covarianceSqrtEquiv (S : Matrix ι ι ℝ) (hS : S.PosDef) :
    LinearMap.det (covarianceSqrtEquiv S hS).toLinearEquiv.toLinearMap =
      Real.sqrt S.det := by
  change (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)).det = _
  rw [det_toEuclideanCLM, hS.posSemidef.det_sqrt, RCLike.sqrt_of_nonneg hS.det_pos.le]
  rfl

/-- A nondegenerate native multivariate Gaussian has its inverse-square-root density. -/
theorem multivariateGaussian_eq_withDensity_prod (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) (hS : S.PosDef) :
    multivariateGaussian m S = volume.withDensity (fun x ↦ ENNReal.ofReal
      ((Real.sqrt S.det)⁻¹ * ∏ i, gaussianPDFReal 0 1
        ((Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹ (x - m)) i))) := by
  let e := covarianceSqrtEquiv S hS
  let p := fun x : EuclideanSpace ℝ ι ↦ ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))
  have hp : Measurable p := by unfold p; fun_prop
  have hf : (fun x ↦ m + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x) =
      (fun x ↦ m + x) ∘ e := rfl
  rw [multivariateGaussian, hf, ← Measure.map_map (by fun_prop) (by fun_prop),
    stdGaussian_eq_withDensity_prod]
  change ((volume.withDensity p).map e).map (fun x ↦ m + x) = _
  rw [map_withDensity_continuousLinearEquiv volume e p hp]
  rw [map_withDensity_const_add volume m _ (by fun_prop)]
  congr 1
  ext x
  dsimp [p, e]
  rw [det_covarianceSqrtEquiv, covarianceSqrtEquiv_symm_apply,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  rfl

open scoped RealInnerProductSpace

theorem norm_inv_covarianceSqrt_sq (S : Matrix ι ι ℝ) (hS : S.PosDef)
    (x : EuclideanSpace ℝ ι) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹ x‖ ^ 2 = x ⬝ᵥ S⁻¹ *ᵥ x := by
  have hself : IsSelfAdjoint (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹) :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)).inv.nonneg.isSelfAdjoint.map _
  rw [← real_inner_self_eq_norm_sq, ← ContinuousLinearMap.adjoint_inner_right,
    IsSelfAdjoint.adjoint_eq hself, ← ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.mul_def, ← map_mul, ← Matrix.mul_inv_rev,
    CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg, Matrix.inner_toEuclideanCLM]

/-- Lebesgue density in terms of the inverse covariance quadratic form. -/
noncomputable def multivariateGaussianPDFReal (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι * (Real.sqrt S.det)⁻¹ *
    Real.exp (-((x - m) ⬝ᵥ S⁻¹ *ᵥ (x - m)) / 2)

theorem multivariateGaussian_eq_withDensity (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) (hS : S.PosDef) :
    multivariateGaussian m S = volume.withDensity
      (fun x ↦ ENNReal.ofReal (multivariateGaussianPDFReal m S x)) := by
  rw [multivariateGaussian_eq_withDensity_prod m S hS]
  congr 1
  ext x
  rw [prod_gaussianPDFReal_zero_one, norm_inv_covarianceSqrt_sq S hS]
  congr 1
  unfold multivariateGaussianPDFReal
  simp only [WithLp.ofLp_sub]
  ring

theorem multivariateGaussianPDFReal_pos (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) (hS : S.PosDef) (x : EuclideanSpace ℝ ι) :
    0 < multivariateGaussianPDFReal m S x := by
  unfold multivariateGaussianPDFReal
  have hdet := hS.det_pos
  positivity

@[fun_prop]
theorem continuous_multivariateGaussianPDFReal (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) : Continuous (multivariateGaussianPDFReal m S) := by
  unfold multivariateGaussianPDFReal dotProduct Matrix.mulVec
  fun_prop

@[fun_prop]
theorem measurable_multivariateGaussianPDFReal (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) : Measurable (multivariateGaussianPDFReal m S) :=
  (continuous_multivariateGaussianPDFReal m S).measurable

theorem lintegral_multivariateGaussianPDFReal (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) (hS : S.PosDef) :
    ∫⁻ x, ENNReal.ofReal (multivariateGaussianPDFReal m S x) = 1 := by
  have h := congrArg (fun μ : Measure (EuclideanSpace ℝ ι) ↦ μ Set.univ)
    (multivariateGaussian_eq_withDensity m S hS)
  simpa only [measure_univ, withDensity_apply _ MeasurableSet.univ, restrict_univ] using h.symm

theorem integrable_multivariateGaussianPDFReal (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) (hS : S.PosDef) : Integrable (multivariateGaussianPDFReal m S) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (measurable_multivariateGaussianPDFReal m S).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ (multivariateGaussianPDFReal_pos m S hS x).le)).mp
  rw [lintegral_multivariateGaussianPDFReal m S hS]
  exact ENNReal.one_ne_top

theorem integral_multivariateGaussianPDFReal (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) (hS : S.PosDef) : ∫ x, multivariateGaussianPDFReal m S x = 1 := by
  have h := ofReal_integral_eq_lintegral_ofReal (integrable_multivariateGaussianPDFReal m S hS)
    (Filter.Eventually.of_forall fun x ↦ (multivariateGaussianPDFReal_pos m S hS x).le)
  rw [lintegral_multivariateGaussianPDFReal m S hS] at h
  have h' := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_one, ENNReal.toReal_ofReal
    (integral_nonneg fun x ↦ (multivariateGaussianPDFReal_pos m S hS x).le)] using h'

theorem multivariateGaussian_absolutelyContinuous (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) (hS : S.PosDef) : multivariateGaussian m S ≪ volume := by
  rw [multivariateGaussian_eq_withDensity m S hS]
  exact withDensity_absolutelyContinuous _ _

theorem rnDeriv_multivariateGaussian_volume (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) (hS : S.PosDef) :
    (multivariateGaussian m S).rnDeriv volume =ᵐ[volume]
      fun x ↦ ENNReal.ofReal (multivariateGaussianPDFReal m S x) := by
  rw [multivariateGaussian_eq_withDensity m S hS]
  exact Measure.rnDeriv_withDensity volume
    (measurable_multivariateGaussianPDFReal m S).ennreal_ofReal

theorem llr_multivariateGaussian_volume (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) (hS : S.PosDef) :
    llr (multivariateGaussian m S) volume =ᵐ[multivariateGaussian m S]
      fun x ↦ Real.log (multivariateGaussianPDFReal m S x) := by
  filter_upwards [(multivariateGaussian_absolutelyContinuous m S hS).ae_le
    (rnDeriv_multivariateGaussian_volume m S hS)] with x hx
  simp only [llr, hx,
    ENNReal.toReal_ofReal (multivariateGaussianPDFReal_pos m S hS x).le]

theorem multivariateGaussian_eq_tilted_log_density (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) (hS : S.PosDef) :
    multivariateGaussian m S = volume.tilted
      (fun x ↦ Real.log (multivariateGaussianPDFReal m S x)) := by
  rw [multivariateGaussian_eq_withDensity m S hS, Measure.tilted]
  simp_rw [Real.exp_log (multivariateGaussianPDFReal_pos m S hS _),
    integral_multivariateGaussianPDFReal m S hS, div_one]

theorem log_multivariateGaussianPDFReal (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) (hS : S.PosDef) (x : EuclideanSpace ℝ ι) :
    Real.log (multivariateGaussianPDFReal m S x) =
      -((Fintype.card ι : ℝ) * Real.log (2 * Real.pi) + Real.log S.det) / 2 -
        ((x - m) ⬝ᵥ S⁻¹ *ᵥ (x - m)) / 2 := by
  have hconst : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hdet : 0 < Real.sqrt S.det := Real.sqrt_pos.mpr hS.det_pos
  rw [multivariateGaussianPDFReal,
    Real.log_mul (mul_ne_zero (pow_ne_zero _ (inv_ne_zero hconst.ne')) (inv_ne_zero hdet.ne'))
      (Real.exp_pos _).ne',
    Real.log_mul (pow_ne_zero _ (inv_ne_zero hconst.ne')) (inv_ne_zero hdet.ne'),
    Real.log_pow, Real.log_inv, Real.log_inv,
    Real.log_sqrt (by positivity), Real.log_sqrt hS.det_pos.le, Real.log_exp]
  ring

theorem integrable_log_multivariateGaussianPDFReal
    {μ : Measure (EuclideanSpace ℝ ι)} [IsFiniteMeasure μ]
    (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (hS : S.PosDef)
    (hquad : Integrable (fun x : EuclideanSpace ℝ ι ↦ (x - m) ⬝ᵥ S⁻¹ *ᵥ (x - m)) μ) :
    Integrable (fun x ↦ Real.log (multivariateGaussianPDFReal m S x)) μ := by
  simp_rw [log_multivariateGaussianPDFReal m S hS]
  exact (integrable_const _).sub (hquad.div_const _)

theorem integral_log_multivariateGaussianPDFReal
    {μ : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure μ]
    (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (hS : S.PosDef)
    (hquad : Integrable (fun x : EuclideanSpace ℝ ι ↦ (x - m) ⬝ᵥ S⁻¹ *ᵥ (x - m)) μ) :
    ∫ x, Real.log (multivariateGaussianPDFReal m S x) ∂μ =
      -((Fintype.card ι : ℝ) * Real.log (2 * Real.pi) + Real.log S.det) / 2 -
        (∫ x, (x - m) ⬝ᵥ S⁻¹ *ᵥ (x - m) ∂μ) / 2 := by
  simp_rw [log_multivariateGaussianPDFReal m S hS]
  rw [integral_sub (integrable_const _) (hquad.div_const _)]
  simp only [integral_const, probReal_univ, one_smul]
  rw [integral_div]

end ProbabilityTheory
