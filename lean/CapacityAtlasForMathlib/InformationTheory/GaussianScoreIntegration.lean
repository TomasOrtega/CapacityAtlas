/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMixtureMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

open MeasureTheory ProbabilityTheory Real Matrix
open scoped BigOperators ENNReal

namespace CapacityAtlas.MeasureInformation

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- Integration by parts for the actual score of a native Gaussian mixture. -/
theorem integral_directionalScore_mul_gaussianMixture
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (v : EuclideanSpace ℝ ι) (g g' : EuclideanSpace ℝ ι → ℝ)
    (hg : ∀ x, HasLineDerivAt ℝ g (g' x) x v)
    (hLp : ∀ a, MemLp g 2 (multivariateGaussian (m a) N))
    (hInt : ∀ a, Integrable g' (multivariateGaussian (m a) N)) :
    (∫ x, directionalScore (gaussianMixturePDFReal w m N) v x * g x
      ∂gaussianMixtureMeasure w m N) =
        -(∫ x, g' x ∂gaussianMixtureMeasure w m N) := by
  have hpg : Integrable (fun x ↦ gaussianMixturePDFReal w m N x * g x) volume :=
    (integrable_gaussianMixturePDFReal_mul_iff w hw m N hN g).mpr
      (integrable_gaussianMixtureMeasure (fun a ↦ (hLp a).integrable (by norm_num)))
  have hpg' : Integrable (fun x ↦ gaussianMixturePDFReal w m N x * g' x) volume :=
    (integrable_gaussianMixturePDFReal_mul_iff w hw m N hN g').mpr
      (integrable_gaussianMixtureMeasure hInt)
  have hdp := integrable_gaussianMixture_lineDeriv_mul w m N hN v g hLp
  have hibp := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℝ) (μ := volume)
    (by simpa only [ContinuousLinearMap.mul_apply', mul_comm] using hpg')
    (by simpa only [ContinuousLinearMap.mul_apply', mul_comm] using hdp)
    (by simpa only [ContinuousLinearMap.mul_apply', mul_comm] using hpg)
    (fun x _ ↦ hg x)
    (fun x _ ↦ hasLineDerivAt_gaussianMixturePDFReal w m N hN x v)
  rw [integral_gaussianMixtureMeasure_eq_density w hw m N hN,
    integral_gaussianMixtureMeasure_eq_density w hw m N hN]
  convert! hibp using 1
  · apply integral_congr_ae
    filter_upwards with x
    simp only [ContinuousLinearMap.mul_apply', directionalScore]
    field_simp [(gaussianMixturePDFReal_pos w hw hw1 m N hN x).ne']
  · congr 1
    apply integral_congr_ae
    filter_upwards with x
    simp only [ContinuousLinearMap.mul_apply', mul_comm]

lemma integral_directionalScore_gaussianMixture
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (v : EuclideanSpace ℝ ι) :
    ∫ x, directionalScore (gaussianMixturePDFReal w m N) v x
      ∂gaussianMixtureMeasure w m N = 0 := by
  simpa only [mul_one, integral_zero, neg_zero] using
    integral_directionalScore_mul_gaussianMixture w hw hw1 m N hN v (fun _ ↦ 1) (fun _ ↦ 0)
      (fun _ ↦ by exact hasDerivAt_const 0 1)
      (fun _ ↦ memLp_const 1) (fun _ ↦ integrable_const 0)

lemma integral_lineDeriv_directionalScore_gaussianMixture
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (v : EuclideanSpace ℝ ι) :
    (∫ x, lineDeriv ℝ (directionalScore (gaussianMixturePDFReal w m N) v) x v
      ∂gaussianMixtureMeasure w m N) =
        -directionalFisherWith volume (gaussianMixturePDFReal w m N) v := by
  have hi := integral_directionalScore_mul_gaussianMixture w hw hw1 m N hN v
    (directionalScore (gaussianMixturePDFReal w m N) v)
    (fun x ↦ lineDeriv ℝ (directionalScore (gaussianMixturePDFReal w m N) v) x v)
    (fun x ↦ (hasLineDerivAt_directionalScore_gaussianMixturePDFReal
      w hw hw1 m N hN v x).lineDifferentiableAt.hasLineDerivAt)
    (fun a ↦ memLp_directionalScore_gaussianMixturePDFReal w hw hw1 m N hN v (m a) N 2 (by norm_num))
    (fun a ↦ (memLp_two_lineDeriv_directionalScore_gaussianMixturePDFReal
      w hw hw1 m N hN v (m a) N).integrable (by norm_num))
  rw [directionalFisherWith_eq_gaussianMixtureMeasure w hw m N hN]
  simp only [← pow_two] at hi
  linarith

lemma integral_directionalScore_mul_multivariateGaussian
    (m : EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (v : EuclideanSpace ℝ ι) (g g' : EuclideanSpace ℝ ι → ℝ)
    (hg : ∀ x, HasLineDerivAt ℝ g (g' x) x v)
    (hLp : MemLp g 2 (multivariateGaussian m N))
    (hInt : Integrable g' (multivariateGaussian m N)) :
    (∫ x, directionalScore (multivariateGaussianPDFReal m N) v x * g x
      ∂multivariateGaussian m N) = -(∫ x, g' x ∂multivariateGaussian m N) := by
  have hp : gaussianMixturePDFReal (fun _ : Unit ↦ 1) (fun _ ↦ m) N =
      multivariateGaussianPDFReal m N := by
    ext x
    simp [gaussianMixturePDFReal]
  simpa only [hp, gaussianMixtureMeasure, Fintype.sum_unique, one_mul,
    ENNReal.ofReal_one, one_smul] using
    integral_directionalScore_mul_gaussianMixture (fun _ : Unit ↦ 1)
      (fun _ ↦ zero_le_one) (by simp) (fun _ ↦ m) N hN v g g' hg
      (fun _ ↦ hLp) (fun _ ↦ hInt)

lemma directionalScore_multivariateGaussianPDFReal (m v x : EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) :
    directionalScore (multivariateGaussianPDFReal m N) v x =
      -(v ⬝ᵥ N⁻¹ *ᵥ (x - m)) := by
  rw [directionalScore, (hasLineDerivAt_multivariateGaussianPDFReal m x v N hN).lineDeriv]
  exact mul_div_cancel_right₀ _ (multivariateGaussianPDFReal_pos m N hN x).ne'

lemma memLp_directionalScore_multivariateGaussianPDFReal (m v k : EuclideanSpace ℝ ι)
    (N S : Matrix ι ι ℝ) (hN : N.PosDef) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (directionalScore (multivariateGaussianPDFReal m N) v) p
      (multivariateGaussian k S) := by
  simp_rw [show directionalScore (multivariateGaussianPDFReal m N) v =
    (fun x : EuclideanSpace ℝ ι ↦ -(v ⬝ᵥ N⁻¹ *ᵥ (x - m))) from
      funext (fun x ↦ directionalScore_multivariateGaussianPDFReal m v x N hN)]
  exact (memLp_gaussian_directional_score m v k N S p hp).neg

lemma integral_directionalScore_multivariateGaussian
    (m : EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (v : EuclideanSpace ℝ ι) :
    ∫ x, directionalScore (multivariateGaussianPDFReal m N) v x
      ∂multivariateGaussian m N = 0 := by
  simpa only [mul_one, integral_zero, neg_zero] using
    integral_directionalScore_mul_multivariateGaussian m N hN v (fun _ ↦ 1) (fun _ ↦ 0)
      (fun _ ↦ hasDerivAt_const 0 1) (memLp_const 1) (integrable_const 0)

lemma memLp_comp_add_const_multivariateGaussian
    {f : EuclideanSpace ℝ ι → ℝ} (hf : Measurable f)
    (m c : EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) {p : ℝ≥0∞}
    (hLp : MemLp f p (multivariateGaussian (m + c) N)) :
    MemLp (fun x ↦ f (x + c)) p (multivariateGaussian m N) := by
  have hm : (multivariateGaussian m N).map (fun x ↦ x + c) =
      multivariateGaussian (m + c) N := by
    simpa only [add_comm] using multivariateGaussian_map_const_add m c N
  exact (memLp_map_measure_iff hf.aestronglyMeasurable (by fun_prop)).mp (hm.symm ▸ hLp)

end CapacityAtlas.MeasureInformation
