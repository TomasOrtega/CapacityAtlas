/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.DifferentialEntropy
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace CapacityAtlas.MeasureInformation

lemma log_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    log (gaussianPDFReal m v x) =
      -(log (2 * π * v) / 2) - (x - m) ^ 2 / (2 * v) := by
  have hvpos : (0 : ℝ) < v := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hconst : 0 < 2 * π * (v : ℝ) := by positivity
  rw [gaussianPDFReal, log_mul (inv_ne_zero (sqrt_pos.mpr hconst).ne') (exp_pos _).ne',
    log_inv, log_sqrt hconst.le, log_exp]
  ring

lemma integrable_log_gaussianPDFReal {μ : Measure ℝ} [IsFiniteMeasure μ]
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (hsq : Integrable (fun x ↦ (x - m) ^ 2) μ) :
    Integrable (fun x ↦ log (gaussianPDFReal m v x)) μ := by
  simp_rw [log_gaussianPDFReal m hv]
  exact (integrable_const _).sub (hsq.div_const _)

lemma integral_log_gaussianPDFReal {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (hsq : Integrable (fun x ↦ (x - m) ^ 2) μ) :
    ∫ x, log (gaussianPDFReal m v x) ∂μ =
      -(log (2 * π * v) / 2) - (∫ x, (x - m) ^ 2 ∂μ) / (2 * v) := by
  simp_rw [log_gaussianPDFReal m hv]
  rw [integral_sub (integrable_const _) (hsq.div_const _), integral_div]
  simp

lemma gaussianReal_eq_tilted_log_density (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal m v = volume.tilted (fun x ↦ log (gaussianPDFReal m v x)) := by
  rw [gaussianReal_of_var_ne_zero m hv, Measure.tilted]
  simp_rw [exp_log (gaussianPDFReal_pos m v _ hv), integral_gaussianPDFReal_eq_one m hv,
    div_one]
  rfl

lemma integrable_centered_sq_gaussianReal (m : ℝ) (v : ℝ≥0) :
    Integrable (fun x ↦ (x - m) ^ 2) (gaussianReal m v) :=
  ((memLp_id_gaussianReal (μ := m) (v := v) 2).sub (memLp_const m)).integrable_sq

lemma integral_centered_sq_gaussianReal (m : ℝ) (v : ℝ≥0) :
    (∫ x, (x - m) ^ 2 ∂gaussianReal m v) = v := by
  simpa only [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] using
    (variance_fun_id_gaussianReal (μ := m) (v := v))

lemma integrable_llr_gaussianReal_volume (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (llr (gaussianReal m v) volume) (gaussianReal m v) := by
  apply (integrable_log_gaussianPDFReal m hv (integrable_centered_sq_gaussianReal m v)).congr
  filter_upwards [(gaussianReal_absolutelyContinuous m hv).ae_le (rnDeriv_gaussianReal m v)]
    with x hx
  simp [llr, hx, toReal_gaussianPDF]

/-- Differential entropy of a nondegenerate real Gaussian, in nats. -/
theorem entropyWith_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    entropyWith (gaussianReal m v) volume = (log (2 * π * v) + 1) / 2 := by
  have hllr : llr (gaussianReal m v) volume =ᵐ[gaussianReal m v]
      fun x ↦ log (gaussianPDFReal m v x) := by
    filter_upwards [(gaussianReal_absolutelyContinuous m hv).ae_le (rnDeriv_gaussianReal m v)]
      with x hx
    simp [llr, hx, toReal_gaussianPDF]
  rw [entropyWith, integral_congr_ae hllr,
    integral_log_gaussianPDFReal m hv (integrable_centered_sq_gaussianReal m v),
    integral_centered_sq_gaussianReal]
  have hvreal : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  field_simp
  ring

/-- A Gaussian comparison bounds entropy using the second moment about its mean. -/
theorem entropyWith_le_gaussian_crossEntropy {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (hlog : Integrable (llr μ volume) μ)
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (hsq : Integrable (fun x ↦ (x - m) ^ 2) μ) :
    entropyWith μ volume ≤
      log (2 * π * v) / 2 + (∫ x, (x - m) ^ 2 ∂μ) / (2 * v) := by
  have hexp : Integrable (fun x ↦ exp (log (gaussianPDFReal m v x))) volume := by
    simpa only [exp_log (gaussianPDFReal_pos m v _ hv)] using integrable_gaussianPDFReal m v
  have h := entropyWith_le_log_partition_sub_integral hμ
    (integrable_log_gaussianPDFReal m hv hsq) hexp hlog
  simp_rw [exp_log (gaussianPDFReal_pos m v _ hv)] at h
  rw [integral_gaussianPDFReal_eq_one m hv, log_one,
    integral_log_gaussianPDFReal m hv hsq] at h
  linarith

theorem entropyWith_le_gaussianReal {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (hlog : Integrable (llr μ volume) μ)
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (hsq : Integrable (fun x ↦ (x - m) ^ 2) μ)
    (hvariance : (∫ x, (x - m) ^ 2 ∂μ) ≤ v) :
    entropyWith μ volume ≤ entropyWith (gaussianReal m v) volume := by
  rw [entropyWith_gaussianReal m hv]
  have hbound := entropyWith_le_gaussian_crossEntropy hμ hlog m hv hsq
  have hvpos : (0 : ℝ) < v := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hratio : (∫ x, (x - m) ^ 2 ∂μ) / (2 * v) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * v)).mpr
    linarith
  linarith

end CapacityAtlas.MeasureInformation
