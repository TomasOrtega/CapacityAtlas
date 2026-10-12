/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMixtureEntropyBounds
import Mathlib.Topology.Instances.Matrix

open MeasureTheory ProbabilityTheory Real Matrix Filter
open scoped BigOperators Topology

namespace CapacityAtlas.MeasureInformation

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

omit [Fintype ι] in
lemma tendsto_normalized_isotropic_covariance (N : Matrix ι ι ℝ) :
    Tendsto (fun t : ℝ ↦ (1 : Matrix ι ι ℝ) + t⁻¹ • N) atTop (𝓝 1) := by
  simpa only [zero_smul, add_zero] using
    tendsto_const_nhds.add ((tendsto_inv_atTop_zero : Tendsto (fun t : ℝ ↦ t⁻¹) atTop (𝓝 0)).smul
      (tendsto_const_nhds (x := N)))

omit [Fintype ι] in
lemma isotropic_covariance_eq_smul (N : Matrix ι ι ℝ) {t : ℝ} (ht : t ≠ 0) :
    N + t • (1 : Matrix ι ι ℝ) = t • ((1 : Matrix ι ι ℝ) + t⁻¹ • N) := by
  rw [smul_add, smul_smul, mul_inv_cancel₀ ht, one_smul, add_comm]

lemma tendsto_inv_isotropic_covariance (N : Matrix ι ι ℝ) (hN : N.PosSemidef) :
    Tendsto (fun t : ℝ ↦ (N + t • (1 : Matrix ι ι ℝ))⁻¹) atTop (𝓝 0) := by
  have hinv : Tendsto (fun t : ℝ ↦ ((1 : Matrix ι ι ℝ) + t⁻¹ • N)⁻¹) atTop (𝓝 1) := by
    have hcont : ContinuousAt Inv.inv (1 : Matrix ι ι ℝ) :=
      continuousAt_matrix_inv 1 (by
        rw [Matrix.det_one, Ring.inverse_eq_inv']
        exact continuousAt_inv₀ one_ne_zero)
    simpa only [Function.comp_def, inv_one] using hcont.tendsto.comp (tendsto_normalized_isotropic_covariance N)
  have hzero : Tendsto (fun t : ℝ ↦ t⁻¹ • ((1 : Matrix ι ι ℝ) + t⁻¹ • N)⁻¹) atTop (𝓝 0) := by
    simpa only [zero_smul] using tendsto_inv_atTop_zero.smul hinv
  apply hzero.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hT := PosDef.one.add_posSemidef (hN.smul (inv_pos.mpr ht).le)
  letI : Invertible t := invertibleOfNonzero ht.ne'
  rw [isotropic_covariance_eq_smul N ht.ne',
    Matrix.inv_smul _ t (isUnit_iff_ne_zero.mpr hT.det_pos.ne'), invOf_eq_inv]

lemma tendsto_logdet_isotropic_covariance_normalized (N : Matrix ι ι ℝ) (hN : N.PosSemidef) :
    Tendsto (fun t : ℝ ↦ log (N + t • (1 : Matrix ι ι ℝ)).det - Fintype.card ι * log t)
      atTop (𝓝 0) := by
  have hdet : Tendsto (fun t : ℝ ↦ ((1 : Matrix ι ι ℝ) + t⁻¹ • N).det) atTop (𝓝 1) := by
    simpa only [Function.comp_def, id_eq, Matrix.det_one] using continuous_id.matrix_det.continuousAt.tendsto.comp
      (tendsto_normalized_isotropic_covariance N)
  have hlog := hdet.log one_ne_zero
  simp only [log_one] at hlog
  apply hlog.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hT := PosDef.one.add_posSemidef (hN.smul (inv_pos.mpr ht).le)
  rw [isotropic_covariance_eq_smul N ht.ne', Matrix.det_smul,
    log_mul (pow_ne_zero _ ht.ne') hT.det_pos.ne', log_pow]
  ring

/-- The centered native Gaussian has its exact large-noise entropy normalization. -/
theorem tendsto_entropyWith_multivariateGaussian_add_isotropic_normalized
    (N : Matrix ι ι ℝ) (hN : N.PosSemidef) :
    Tendsto (fun t : ℝ ↦ entropyWith
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) (N + t • (1 : Matrix ι ι ℝ))) volume -
        (Fintype.card ι : ℝ) / 2 * log t)
      atTop (𝓝 ((Fintype.card ι : ℝ) / 2 * (log (2 * π) + 1))) := by
  have hl := (tendsto_const_nhds (x := (Fintype.card ι : ℝ) * (log (2 * π) + 1))).add
    (tendsto_logdet_isotropic_covariance_normalized N hN)
  have hlim := hl.div_const 2
  simp only [add_zero] at hlim
  have hconst : (Fintype.card ι : ℝ) * (log (2 * π) + 1) / 2 =
      (Fintype.card ι : ℝ) / 2 * (log (2 * π) + 1) := by ring
  rw [hconst] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [entropyWith_multivariateGaussian _ _ (PosDef.posSemidef_add hN (PosDef.one.smul ht))]
  ring

lemma tendsto_gaussianMixture_isotropic_mean_penalty
    (w : α → ℝ) (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosSemidef) :
    Tendsto (fun t : ℝ ↦ (∑ a, w a *
      (m a ⬝ᵥ (N + t • (1 : Matrix ι ι ℝ))⁻¹ *ᵥ m a)) / 2) atTop (𝓝 0) := by
  have hrow (a : α) : Tendsto (fun t : ℝ ↦ w a *
      (m a ⬝ᵥ (N + t • (1 : Matrix ι ι ℝ))⁻¹ *ᵥ m a)) atTop (𝓝 0) := by
    have hcont : Continuous (fun S : Matrix ι ι ℝ ↦ w a * (m a ⬝ᵥ S *ᵥ m a)) := by
      unfold dotProduct Matrix.mulVec
      fun_prop
    simpa only [Function.comp_def, Matrix.zero_mulVec, dotProduct_zero, mul_zero] using
      hcont.continuousAt.tendsto.comp (tendsto_inv_isotropic_covariance N hN)
  simpa only [Finset.sum_const_zero, zero_div] using
    (tendsto_finsetSum Finset.univ (fun a _ ↦ hrow a)).div_const 2

/-- Finite native mixtures have the same normalized entropy limit as their Gaussian noise. -/
theorem tendsto_entropyWith_gaussianMixtureMeasure_add_isotropic_normalized
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosSemidef) :
    Tendsto (fun t : ℝ ↦ entropyWith
      (gaussianMixtureMeasure w m (N + t • (1 : Matrix ι ι ℝ))) volume -
        (Fintype.card ι : ℝ) / 2 * log t)
      atTop (𝓝 ((Fintype.card ι : ℝ) / 2 * (log (2 * π) + 1))) := by
  have hgap : Tendsto (fun t : ℝ ↦
      entropyWith (gaussianMixtureMeasure w m (N + t • (1 : Matrix ι ι ℝ))) volume -
        entropyWith (multivariateGaussian (0 : EuclideanSpace ℝ ι) (N + t • (1 : Matrix ι ι ℝ))) volume)
      atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (tendsto_gaussianMixture_isotropic_mean_penalty w m N hN)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      exact sub_nonneg.mpr (entropyWith_gaussianMixtureMeasure_ge_noise w hw hw1 m _
        (PosDef.posSemidef_add hN (PosDef.one.smul ht)))
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      exact sub_le_iff_le_add'.mpr (entropyWith_gaussianMixtureMeasure_le_noise_add w hw hw1 m _
        (PosDef.posSemidef_add hN (PosDef.one.smul ht)))
  have h := (tendsto_entropyWith_multivariateGaussian_add_isotropic_normalized N hN).add hgap
  simp only [add_zero] at h
  convert! h using 1
  funext t
  ring

theorem tendsto_entropyWith_gaussianMixtureMeasure_add_isotropic_sub_log
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef) :
    Tendsto (fun t : ℝ ↦ entropyWith
      (gaussianMixtureMeasure w m (N + t • (1 : Matrix ι ι ℝ))) volume -
        (Fintype.card ι : ℝ) / 2 * log t)
      atTop (𝓝 ((Fintype.card ι : ℝ) / 2 * (log (2 * π) + 1))) :=
  tendsto_entropyWith_gaussianMixtureMeasure_add_isotropic_normalized w hw hw1 m N hN.posSemidef

end CapacityAtlas.MeasureInformation
