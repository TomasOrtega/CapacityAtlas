/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMixtureMeasure
import CapacityAtlasForMathlib.InformationTheory.GaussianDiagonalDeBruijn

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real Matrix
open scoped BigOperators ENNReal NNReal

namespace CapacityAtlas.MeasureInformation

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

lemma gaussianMixtureMeasure_map_matrix (w : α → ℝ) (m : α → EuclideanSpace ℝ ι)
    (N A : Matrix ι ι ℝ) (hN : N.PosSemidef) :
    (gaussianMixtureMeasure w m N).map (fun x ↦ A.toEuclideanLin x) =
      gaussianMixtureMeasure w (fun a ↦ A.toEuclideanLin (m a)) (A * N * A.transpose) := by
  unfold gaussianMixtureMeasure
  rw [← Measure.sum_fintype, Measure.map_sum (by fun_prop), Measure.sum_fintype]
  simp_rw [Measure.map_smul, multivariateGaussian_map_matrix A _ N hN]

lemma gaussianMixtureMeasure_absolutelyContinuous (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef) :
    gaussianMixtureMeasure w m N ≪ volume := by
  rw [gaussianMixtureMeasure_eq_withDensity w hw m N hN]
  exact withDensity_absolutelyContinuous _ _

lemma integrable_llr_gaussianMixtureMeasure (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hw1 : ∑ a, w a = 1) (m : α → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) :
    Integrable (llr (gaussianMixtureMeasure w m N) volume) (gaussianMixtureMeasure w m N) := by
  obtain ⟨j, _, hj⟩ := (Finset.sum_pos_iff_of_nonneg (fun a (_ : a ∈ Finset.univ) ↦ hw a)).mp
    (show 0 < ∑ a, w a by rw [hw1]; norm_num)
  have hl : Integrable (fun x ↦ log (gaussianMixturePDFReal w m N x))
      (gaussianMixtureMeasure w m N) := by
    apply integrable_gaussianMixtureMeasure
    intro a
    simpa only [one_smul] using
      (memLp_two_log_gaussianMixturePDFReal_smul w hw hw1 m N hN j hj zero_lt_one (m a) N).integrable
        (by norm_num : (1 : ENNReal) ≤ 2)
  have hllr := llr_eq_log_density (gaussianMixtureMeasure w m N) volume
    (measurable_gaussianMixturePDFReal w m N).ennreal_ofReal
    (gaussianMixtureMeasure_eq_withDensity w hw m N hN)
  have heq : llr (gaussianMixtureMeasure w m N) volume =ᵐ[gaussianMixtureMeasure w m N]
      fun x ↦ log (gaussianMixturePDFReal w m N x) := by
    filter_upwards [hllr] with x hx
    simpa only [ENNReal.toReal_ofReal (gaussianMixturePDFReal_pos w hw hw1 m N hN x).le] using hx
  exact hl.congr heq.symm

omit [Fintype α] [DecidableEq ι] in
lemma entropyWith_map_continuousLinearEquiv
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hac : μ ≪ volume) (hlog : Integrable (llr μ volume) μ)
    (e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι) :
    entropyWith (μ.map e) volume = entropyWith μ volume + log |e.toLinearEquiv.toLinearMap.det| := by
  let c : ℝ≥0 := ⟨|e.toLinearEquiv.toLinearMap.det⁻¹|, abs_nonneg _⟩
  have hc : c ≠ 0 := by
    apply NNReal.coe_ne_zero.mp
    exact abs_ne_zero.mpr (inv_ne_zero e.toLinearEquiv.isUnit_det'.ne_zero)
  have hmap : (volume : Measure (EuclideanSpace ℝ ι)).map e = c • volume := by
    have hm := map_linearMap_addHaar_eq_smul_addHaar
      (volume : Measure (EuclideanSpace ℝ ι)) e.toLinearEquiv.isUnit_det'.ne_zero
    change (volume : Measure (EuclideanSpace ℝ ι)).map e = (c : ENNReal) • volume
    have hcval : (c : ENNReal) = ENNReal.ofReal |e.toLinearEquiv.toLinearMap.det⁻¹| :=
      (ENNReal.ofReal_coe_nnreal (p := c)).symm
    rw [hcval]
    exact hm
  have h := entropyWith_map_of_map_reference_eq_smul hac hlog
    e.toHomeomorph.measurableEmbedding c hc hmap
  change entropyWith (μ.map e) volume = entropyWith μ volume - log |e.toLinearEquiv.toLinearMap.det⁻¹| at h
  simpa only [abs_inv, log_inv, sub_neg_eq_add] using h

lemma entropyWith_gaussianMixtureMeasure_map_matrix
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N A : Matrix ι ι ℝ)
    (hN : N.PosDef) (hA : A.det ≠ 0) :
    entropyWith (gaussianMixtureMeasure w (fun a ↦ A.toEuclideanLin (m a))
      (A * N * A.transpose)) volume =
        entropyWith (gaussianMixtureMeasure w m N) volume + log |A.det| := by
  letI := isProbabilityMeasure_gaussianMixtureMeasure w hw hw1 m N
  let e := (Matrix.toEuclideanCLM (𝕜 := ℝ) A).toContinuousLinearEquivOfDetNeZero
    (by rw [det_toEuclideanCLM]; exact hA)
  have he : (e : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) = fun x ↦ A.toEuclideanLin x := rfl
  have hdet : e.toLinearEquiv.toLinearMap.det = A.det := det_toEuclideanCLM A
  rw [← gaussianMixtureMeasure_map_matrix w m N A hN.posSemidef, ← he,
    entropyWith_map_continuousLinearEquiv _
      (gaussianMixtureMeasure_absolutelyContinuous w hw m N hN)
      (integrable_llr_gaussianMixtureMeasure w hw hw1 m N hN), hdet]


lemma posDef_covariance_congruence (N A : Matrix ι ι ℝ)
    (hN : N.PosDef) (hA : A.det ≠ 0) : (A * N * A.transpose).PosDef := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    hN.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA)))

@[fun_prop]
lemma continuous_gaussianMixturePDFReal (w : α → ℝ) (m : α → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) : Continuous (gaussianMixturePDFReal w m N) := by
  unfold gaussianMixturePDFReal
  fun_prop

/-- The native mixture density obeys the pointwise linear Jacobian formula. -/
lemma gaussianMixturePDFReal_matrix_apply (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hw1 : ∑ a, w a = 1) (m : α → EuclideanSpace ℝ ι)
    (N A : Matrix ι ι ℝ) (hN : N.PosDef) (hA : A.det ≠ 0) (x : EuclideanSpace ℝ ι) :
    gaussianMixturePDFReal w (fun a ↦ A.toEuclideanLin (m a)) (A * N * A.transpose)
      (A.toEuclideanLin x) = |A.det|⁻¹ * gaussianMixturePDFReal w m N x := by
  let e := (Matrix.toEuclideanCLM (𝕜 := ℝ) A).toContinuousLinearEquivOfDetNeZero
    (by rw [det_toEuclideanCLM]; exact hA)
  let p := gaussianMixturePDFReal w m N
  let q := gaussianMixturePDFReal w (fun a ↦ A.toEuclideanLin (m a)) (A * N * A.transpose)
  have hdet : e.toLinearEquiv.toLinearMap.det = A.det := det_toEuclideanCLM A
  have hcov := posDef_covariance_congruence N A hN hA
  have hmap : ((volume : Measure (EuclideanSpace ℝ ι)).withDensity (fun y ↦ ENNReal.ofReal (p y))).map e =
      volume.withDensity (fun y ↦ ENNReal.ofReal (q y)) := by
    rw [← gaussianMixtureMeasure_eq_withDensity w hw m N hN]
    exact (gaussianMixtureMeasure_map_matrix w m N A hN.posSemidef).trans
      (gaussianMixtureMeasure_eq_withDensity w hw _ _ hcov)
  rw [map_withDensity_continuousLinearEquiv volume e _ (by dsimp [p]; fun_prop), hdet] at hmap
  have hae := (withDensity_eq_iff_of_sigmaFinite (by fun_prop) (by dsimp [q]; fun_prop)).mp hmap
  have haereal : (fun y ↦ |A.det⁻¹| * p (e.symm y)) =ᵐ[volume] q := by
    filter_upwards [hae] with y hy
    rw [← ENNReal.ofReal_mul (abs_nonneg _)] at hy
    have hreal := congrArg ENNReal.toReal hy
    dsimp [p, q] at hreal ⊢
    simpa only [ENNReal.toReal_ofReal (mul_nonneg (abs_nonneg _)
        (gaussianMixturePDFReal_pos w hw hw1 m N hN (e.symm y)).le),
      ENNReal.toReal_ofReal (gaussianMixturePDFReal_pos w hw hw1 _ _ hcov y).le] using hreal
  have heq : (fun y ↦ |A.det⁻¹| * p (e.symm y)) = q :=
    (Continuous.ae_eq_iff_eq (μ := volume) (by dsimp [p]; fun_prop) (by dsimp [q]; fun_prop)).mp haereal
  have hx := congrFun heq (e x)
  rw [e.symm_apply_apply, abs_inv] at hx
  have he (y : EuclideanSpace ℝ ι) : e y = A.toEuclideanLin y := rfl
  simpa only [he] using hx.symm

lemma directionalScore_gaussianMixturePDFReal_matrix_apply
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N A : Matrix ι ι ℝ)
    (hN : N.PosDef) (hA : A.det ≠ 0) (x v : EuclideanSpace ℝ ι) :
    directionalScore (gaussianMixturePDFReal w (fun a ↦ A.toEuclideanLin (m a))
      (A * N * A.transpose)) (A.toEuclideanLin v) (A.toEuclideanLin x) =
        directionalScore (gaussianMixturePDFReal w m N) v x := by
  let q := gaussianMixturePDFReal w (fun a ↦ A.toEuclideanLin (m a)) (A * N * A.transpose)
  have heq : q ∘ A.toEuclideanLin = fun y ↦ |A.det|⁻¹ * gaussianMixturePDFReal w m N y := by
    funext y
    exact gaussianMixturePDFReal_matrix_apply w hw hw1 m N A hN hA y
  have hd : HasLineDerivAt ℝ (q ∘ A.toEuclideanLin)
      (|A.det|⁻¹ * lineDeriv ℝ (gaussianMixturePDFReal w m N) x v) x v := by
    rw [heq]
    exact (hasLineDerivAt_gaussianMixturePDFReal w m N hN x v).const_mul _
  have hl := hd.of_comp.lineDeriv
  unfold directionalScore
  rw [hl, gaussianMixturePDFReal_matrix_apply w hw hw1 m N A hN hA x]
  exact mul_div_mul_left _ _ (inv_ne_zero (abs_ne_zero.mpr hA))

/-- Linear transport preserves Fisher information in the transported direction. -/
lemma directionalFisherWith_gaussianMixturePDFReal_matrix
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N A : Matrix ι ι ℝ)
    (hN : N.PosDef) (hA : A.det ≠ 0) (v : EuclideanSpace ℝ ι) :
    directionalFisherWith volume (gaussianMixturePDFReal w (fun a ↦ A.toEuclideanLin (m a))
      (A * N * A.transpose)) (A.toEuclideanLin v) =
        directionalFisherWith volume (gaussianMixturePDFReal w m N) v := by
  rw [directionalFisherWith_eq_gaussianMixtureMeasure w hw _ _
      (posDef_covariance_congruence N A hN hA),
    ← gaussianMixtureMeasure_map_matrix w m N A hN.posSemidef,
    integral_map (by fun_prop)
      ((measurable_directionalScore_gaussianMixturePDFReal w _ _
        (posDef_covariance_congruence N A hN hA) (A.toEuclideanLin v)).pow_const 2).aestronglyMeasurable,
    directionalFisherWith_eq_gaussianMixtureMeasure w hw m N hN]
  apply integral_congr_ae
  filter_upwards with x
  rw [directionalScore_gaussianMixturePDFReal_matrix_apply w hw hw1 m N A hN hA x v]

end CapacityAtlas.MeasureInformation
