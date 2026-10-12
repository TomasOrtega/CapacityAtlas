/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMixtureScore

open MeasureTheory ProbabilityTheory Real Matrix
open scoped BigOperators ENNReal

namespace CapacityAtlas.MeasureInformation

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

noncomputable def gaussianMixtureMeasure (w : α → ℝ) (m : α → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) : Measure (EuclideanSpace ℝ ι) :=
  ∑ a, ENNReal.ofReal (w a) • multivariateGaussian (m a) N

instance isFiniteMeasure_gaussianMixtureMeasure (w : α → ℝ)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) :
    IsFiniteMeasure (gaussianMixtureMeasure w m N) := by
  refine ⟨?_⟩
  simp only [gaussianMixtureMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.mpr (fun a _ ↦ ENNReal.ofReal_lt_top)

lemma isProbabilityMeasure_gaussianMixtureMeasure (w : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) :
    IsProbabilityMeasure (gaussianMixtureMeasure w m N) := by
  apply isProbabilityMeasure_iff.mpr
  simp only [gaussianMixtureMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ ↦ hw a), hw1, ENNReal.ofReal_one]

lemma integrable_gaussianMixtureMeasure {w : α → ℝ} {m : α → EuclideanSpace ℝ ι}
    {N : Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ}
    (hf : ∀ a, Integrable f (multivariateGaussian (m a) N)) :
    Integrable f (gaussianMixtureMeasure w m N) := by
  apply integrable_finsetSum_measure.mpr
  intro a _
  exact (hf a).smul_measure ENNReal.ofReal_ne_top

lemma integral_gaussianMixtureMeasure (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (f : EuclideanSpace ℝ ι → ℝ)
    (hf : ∀ a, Integrable f (multivariateGaussian (m a) N)) :
    ∫ x, f x ∂gaussianMixtureMeasure w m N =
      ∑ a, w a * ∫ x, f x ∂multivariateGaussian (m a) N := by
  rw [gaussianMixtureMeasure, integral_finsetSum_measure
    (fun a _ ↦ (hf a).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, ENNReal.toReal_ofReal (hw _), smul_eq_mul]

lemma memLp_two_gaussianMixtureMeasure {w : α → ℝ} {m : α → EuclideanSpace ℝ ι}
    {N : Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ} (hf : Measurable f)
    (hrow : ∀ a, MemLp f 2 (multivariateGaussian (m a) N)) :
    MemLp f 2 (gaussianMixtureMeasure w m N) := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
  exact integrable_gaussianMixtureMeasure
    (fun a ↦ (memLp_two_iff_integrable_sq (hrow a).aestronglyMeasurable).mp (hrow a))

lemma gaussianMixtureMeasure_eq_withDensity (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef) :
    gaussianMixtureMeasure w m N =
      volume.withDensity (fun x ↦ ENNReal.ofReal (gaussianMixturePDFReal w m N x)) := by
  have hpdf : (fun x ↦ ENNReal.ofReal (gaussianMixturePDFReal w m N x)) =
      ∑ a, ENNReal.ofReal (w a) •
        (fun x ↦ ENNReal.ofReal (multivariateGaussianPDFReal (m a) N x)) := by
    ext x
    simp only [gaussianMixturePDFReal, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [ENNReal.ofReal_sum_of_nonneg (fun a _ ↦
      mul_nonneg (hw a) (multivariateGaussianPDFReal_pos (m a) N hN x).le)]
    simp only [ENNReal.ofReal_mul (hw _)]
  rw [hpdf, ← tsum_fintype (L := SummationFilter.unconditional α), withDensity_tsum]
  · rw [Measure.sum_fintype]
    unfold gaussianMixtureMeasure
    apply Finset.sum_congr rfl
    intro a _
    rw [withDensity_smul _ (measurable_multivariateGaussianPDFReal (m a) N).ennreal_ofReal,
      ← multivariateGaussian_eq_withDensity (m a) N hN]
  · intro a
    exact measurable_const.mul (measurable_multivariateGaussianPDFReal (m a) N).ennreal_ofReal

lemma integral_gaussianMixtureMeasure_eq_density (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (f : EuclideanSpace ℝ ι → ℝ) :
    ∫ x, f x ∂gaussianMixtureMeasure w m N =
      ∫ x, gaussianMixturePDFReal w m N x * f x := by
  rw [gaussianMixtureMeasure_eq_withDensity w hw m N hN,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_gaussianMixturePDFReal w m N).ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal, smul_eq_mul]
  exact Finset.sum_nonneg (fun a _ ↦
    mul_nonneg (hw a) (multivariateGaussianPDFReal_pos (m a) N hN x).le)

lemma directionalFisherWith_eq_gaussianMixtureMeasure (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (v : EuclideanSpace ℝ ι) :
    directionalFisherWith volume (gaussianMixturePDFReal w m N) v =
      ∫ x, directionalScore (gaussianMixturePDFReal w m N) v x ^ 2
        ∂gaussianMixtureMeasure w m N := by
  rw [directionalFisherWith_eq_integral_score_sq,
    integral_gaussianMixtureMeasure_eq_density w hw m N hN]

lemma gaussianMixtureMeasure_conv (w : α → ℝ) (m : α → EuclideanSpace ℝ ι)
    (n : EuclideanSpace ℝ ι) (N S : Matrix ι ι ℝ) (hN : N.PosSemidef) (hS : S.PosSemidef) :
    gaussianMixtureMeasure w m N ∗ multivariateGaussian n S =
      gaussianMixtureMeasure w (fun a ↦ m a + n) (N + S) := by
  unfold gaussianMixtureMeasure
  simp_rw [Measure.conv, ← Measure.sum_fintype, Measure.prod_sum_left,
    Measure.map_sum measurable_add.aemeasurable, Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro a _
  change (ENNReal.ofReal (w a) • multivariateGaussian (m a) N) ∗ multivariateGaussian n S = _
  rw [Measure.conv_smul_left, multivariateGaussian_conv _ _ _ _ hN hS]

lemma integrable_gaussianMixturePDFReal_mul_iff (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (f : EuclideanSpace ℝ ι → ℝ) :
    Integrable (fun x ↦ gaussianMixturePDFReal w m N x * f x) volume ↔
      Integrable f (gaussianMixtureMeasure w m N) := by
  rw [gaussianMixtureMeasure_eq_withDensity w hw m N hN,
    integrable_withDensity_iff_integrable_smul'
      (measurable_gaussianMixturePDFReal w m N).ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  have hpos (x) : 0 ≤ gaussianMixturePDFReal w m N x :=
    Finset.sum_nonneg (fun a _ ↦
      mul_nonneg (hw a) (multivariateGaussianPDFReal_pos (m a) N hN x).le)
  simp only [ENNReal.toReal_ofReal (hpos _), smul_eq_mul]

lemma gaussianMixtureMeasure_map_const_add (w : α → ℝ)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (c : EuclideanSpace ℝ ι) :
    (gaussianMixtureMeasure w m N).map (fun x ↦ c + x) =
      gaussianMixtureMeasure w (fun a ↦ c + m a) N := by
  unfold gaussianMixtureMeasure
  rw [Measure.map_finset_sum' (by fun_prop)]
  simp_rw [Measure.map_smul, multivariateGaussian_map_const_add]

end CapacityAtlas.MeasureInformation
