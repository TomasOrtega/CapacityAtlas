/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianFisherInformation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open MeasureTheory ProbabilityTheory Real Matrix Filter
open scoped Topology
open scoped BigOperators

namespace CapacityAtlas.MeasureInformation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma log_multivariateGaussianPDFReal_smul (m x : EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) {t : ℝ} (ht : 0 < t) :
    log (multivariateGaussianPDFReal m (t • N) x) =
      -((Fintype.card ι : ℝ) * log (2 * π) + Fintype.card ι * log t + log N.det) / 2 -
        ((x - m) ⬝ᵥ N⁻¹ *ᵥ (x - m)) / (2 * t) := by
  letI : Invertible t := invertibleOfNonzero ht.ne'
  rw [log_multivariateGaussianPDFReal m (t • N) (hN.smul ht), Matrix.det_smul,
    log_mul (pow_pos ht _).ne' hN.det_pos.ne', log_pow,
    Matrix.inv_smul (A := N) t (isUnit_iff_ne_zero.mpr hN.det_pos.ne')]
  simp only [invOf_eq_inv, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  ring

/-- The native Gaussian log density is differentiable along covariance scaling. -/
theorem hasDerivAt_log_multivariateGaussianPDFReal_smul (m x : EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ log (multivariateGaussianPDFReal m (s • N) x))
      (-Fintype.card ι / (2 * t) +
        ((x - m) ⬝ᵥ N⁻¹ *ᵥ (x - m)) / (2 * t ^ 2)) t := by
  have heq : (fun s ↦ log (multivariateGaussianPDFReal m (s • N) x)) =ᶠ[𝓝 t]
      (fun s ↦ -((Fintype.card ι : ℝ) * log (2 * π) +
        Fintype.card ι * log s + log N.det) / 2 -
          ((x - m) ⬝ᵥ N⁻¹ *ᵥ (x - m)) / (2 * s)) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact log_multivariateGaussianPDFReal_smul m x N hN hs
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  have hlog := ((hasDerivAt_const t ((Fintype.card ι : ℝ) * log (2 * π))).add
    ((hasDerivAt_log ht.ne').const_mul (Fintype.card ι : ℝ))).add
      (hasDerivAt_const t (log N.det))
  have hquad := (hasDerivAt_const t ((x - m) ⬝ᵥ N⁻¹ *ᵥ (x - m))).div
    ((hasDerivAt_id t).const_mul 2) (mul_ne_zero (by norm_num) ht.ne')
  convert! (hlog.neg.div_const 2).sub hquad using 1
  simp only [id_eq]
  field_simp
  ring

/-- The covariance-time derivative is a quadratic polynomial times the native density. -/
theorem hasDerivAt_multivariateGaussianPDFReal_smul (m x : EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ multivariateGaussianPDFReal m (s • N) x)
      ((-Fintype.card ι / (2 * t) +
        ((x - m) ⬝ᵥ N⁻¹ *ᵥ (x - m)) / (2 * t ^ 2)) *
          multivariateGaussianPDFReal m (t • N) x) t := by
  have heq : (fun s ↦ multivariateGaussianPDFReal m (s • N) x) =ᶠ[𝓝 t]
      (fun s ↦ exp (log (multivariateGaussianPDFReal m (s • N) x))) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact (exp_log (multivariateGaussianPDFReal_pos m (s • N) (hN.smul hs) x)).symm
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  simpa only [exp_log (multivariateGaussianPDFReal_pos m (t • N) (hN.smul ht) x),
    mul_comm] using (hasDerivAt_log_multivariateGaussianPDFReal_smul m x N hN ht).exp

lemma lineDeriv_lineDeriv_multivariateGaussianPDFReal_isotropic
    (m x : EuclideanSpace ℝ ι) {t : ℝ} (ht : 0 < t) (i : ι) :
    lineDeriv ℝ (fun y ↦ lineDeriv ℝ
      (multivariateGaussianPDFReal m (t • (1 : Matrix ι ι ℝ))) y
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) =
      (((x i - m i) / t) ^ 2 - 1 / t) *
        multivariateGaussianPDFReal m (t • (1 : Matrix ι ι ℝ)) x := by
  letI : Invertible t := invertibleOfNonzero ht.ne'
  rw [(hasLineDerivAt_lineDeriv_multivariateGaussianPDFReal m x
    (EuclideanSpace.single i 1) (t • (1 : Matrix ι ι ℝ))
      (Matrix.PosDef.one.smul ht)).lineDeriv,
    Matrix.inv_smul (A := (1 : Matrix ι ι ℝ)) t (by simp)]
  simp only [invOf_eq_inv, inv_one, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, smul_eq_mul, PiLp.ofLp_single, single_one_dotProduct,
    Pi.sub_apply, Pi.single_eq_same, mul_one, div_eq_mul_inv,
    mul_comm]

/-- The native isotropic Gaussian density solves the heat equation. -/
theorem hasDerivAt_multivariateGaussianPDFReal_heat (m x : EuclideanSpace ℝ ι)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ multivariateGaussianPDFReal m (s • (1 : Matrix ι ι ℝ)) x)
      ((1 / 2 : ℝ) * ∑ i, lineDeriv ℝ (fun y ↦ lineDeriv ℝ
        (multivariateGaussianPDFReal m (t • (1 : Matrix ι ι ℝ))) y
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) t := by
  apply (hasDerivAt_multivariateGaussianPDFReal_smul m x (1 : Matrix ι ι ℝ)
    Matrix.PosDef.one ht).congr_deriv
  have hq : (x - m) ⬝ᵥ (1 : Matrix ι ι ℝ)⁻¹ *ᵥ (x - m) =
      ∑ i, (x i - m i) ^ 2 := by
    simp [dotProduct, pow_two]
  rw [hq]
  simp_rw [lineDeriv_lineDeriv_multivariateGaussianPDFReal_isotropic m x ht,
    div_pow]
  rw [← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.sum_div]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

section FiniteMixture

variable {α : Type*} [Fintype α]

lemma lineDeriv_lineDeriv_gaussian_mixture (w : α → ℝ) (m : α → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) (x v : EuclideanSpace ℝ ι) :
    lineDeriv ℝ (fun y ↦ lineDeriv ℝ
      (fun z ↦ ∑ a, w a * multivariateGaussianPDFReal (m a) N z) y v) x v =
      ∑ a, w a * lineDeriv ℝ
        (fun y ↦ lineDeriv ℝ (multivariateGaussianPDFReal (m a) N) y v) x v := by
  have hfirst (y : EuclideanSpace ℝ ι) :=
    (hasLineDerivAt_weighted_sum w (fun a ↦ multivariateGaussianPDFReal (m a) N)
      (fun a z ↦ lineDeriv ℝ (multivariateGaussianPDFReal (m a) N) z v) y v
      (fun a ↦ (hasLineDerivAt_multivariateGaussianPDFReal (m a) y v N hN).lineDifferentiableAt.hasLineDerivAt)).lineDeriv
  simp_rw [hfirst]
  exact (hasLineDerivAt_weighted_sum w
    (fun a y ↦ lineDeriv ℝ (multivariateGaussianPDFReal (m a) N) y v)
    (fun a z ↦ lineDeriv ℝ
      (fun y ↦ lineDeriv ℝ (multivariateGaussianPDFReal (m a) N) y v) z v) x v
    (fun a ↦ (hasLineDerivAt_lineDeriv_multivariateGaussianPDFReal (m a) x v N hN).lineDifferentiableAt.hasLineDerivAt)).lineDeriv

/-- Finite Gaussian mixtures satisfy the same pointwise heat equation as each kernel. -/
theorem hasDerivAt_gaussian_mixture_heat (w : α → ℝ) (m : α → EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ ∑ a, w a *
      multivariateGaussianPDFReal (m a) (s • (1 : Matrix ι ι ℝ)) x)
      ((1 / 2 : ℝ) * ∑ i, lineDeriv ℝ (fun y ↦ lineDeriv ℝ
        (fun z ↦ ∑ a, w a * multivariateGaussianPDFReal (m a)
          (t • (1 : Matrix ι ι ℝ)) z) y (EuclideanSpace.single i 1)) x
            (EuclideanSpace.single i 1)) t := by
  convert! HasDerivAt.fun_sum (fun a (_ : a ∈ Finset.univ) ↦
    (hasDerivAt_multivariateGaussianPDFReal_heat (m a) x ht).const_mul (w a)) using 1
  simp_rw [lineDeriv_lineDeriv_gaussian_mixture w m _ (Matrix.PosDef.one.smul ht)]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  ring

end FiniteMixture

end CapacityAtlas.MeasureInformation
