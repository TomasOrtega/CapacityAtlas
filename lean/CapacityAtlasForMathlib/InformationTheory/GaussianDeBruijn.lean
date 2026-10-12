/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianEntropyDerivative
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

open MeasureTheory ProbabilityTheory Real Matrix Filter
open scoped BigOperators Topology

namespace CapacityAtlas.MeasureInformation

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

lemma lineDeriv_gaussianMixturePDFReal_eq_sum (w : α → ℝ) (m : α → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) (x v : EuclideanSpace ℝ ι) :
    lineDeriv ℝ (gaussianMixturePDFReal w m N) x v =
      ∑ a, w a * lineDeriv ℝ (multivariateGaussianPDFReal (m a) N) x v := by
  exact (hasLineDerivAt_weighted_sum w (fun a ↦ multivariateGaussianPDFReal (m a) N)
    (fun a z ↦ lineDeriv ℝ (multivariateGaussianPDFReal (m a) N) z v) x v
    (fun a ↦ (hasLineDerivAt_multivariateGaussianPDFReal (m a) x v N hN).lineDifferentiableAt.hasLineDerivAt)).lineDeriv

lemma hasLineDerivAt_gaussianMixturePDFReal (w : α → ℝ) (m : α → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) (x v : EuclideanSpace ℝ ι) :
    HasLineDerivAt ℝ (gaussianMixturePDFReal w m N)
      (lineDeriv ℝ (gaussianMixturePDFReal w m N) x v) x v := by
  rw [lineDeriv_gaussianMixturePDFReal_eq_sum w m N hN]
  exact hasLineDerivAt_weighted_sum w (fun a ↦ multivariateGaussianPDFReal (m a) N)
    (fun a z ↦ lineDeriv ℝ (multivariateGaussianPDFReal (m a) N) z v) x v
    (fun a ↦ (hasLineDerivAt_multivariateGaussianPDFReal (m a) x v N hN).lineDifferentiableAt.hasLineDerivAt)

lemma hasLineDerivAt_lineDeriv_gaussianMixturePDFReal (w : α → ℝ)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (x v : EuclideanSpace ℝ ι) :
    HasLineDerivAt ℝ (fun y ↦ lineDeriv ℝ (gaussianMixturePDFReal w m N) y v)
      (lineDeriv ℝ (fun y ↦ lineDeriv ℝ (gaussianMixturePDFReal w m N) y v) x v) x v := by
  have hd := hasLineDerivAt_weighted_sum w
    (fun a y ↦ lineDeriv ℝ (multivariateGaussianPDFReal (m a) N) y v)
    (fun a z ↦ lineDeriv ℝ
      (fun y ↦ lineDeriv ℝ (multivariateGaussianPDFReal (m a) N) y v) z v) x v
    (fun a ↦ (hasLineDerivAt_lineDeriv_multivariateGaussianPDFReal (m a) x v N hN).lineDifferentiableAt.hasLineDerivAt)
  apply LineDifferentiableAt.hasLineDerivAt
  simpa only [← lineDeriv_gaussianMixturePDFReal_eq_sum w m N hN] using hd.lineDifferentiableAt

lemma memLp_two_gaussian_directional_score (m v k : EuclideanSpace ℝ ι)
    (N S : Matrix ι ι ℝ) :
    MemLp (fun x : EuclideanSpace ℝ ι ↦ v ⬝ᵥ N⁻¹ *ᵥ (x - m)) 2
      (multivariateGaussian k S) := by
  simp_rw [Matrix.dotProduct_mulVec]
  simp only [dotProduct, Pi.sub_apply]
  apply memLp_finsetSum
  intro i _
  exact ((memLp_eval_multivariateGaussian k S i).sub (memLp_const (m i))).const_mul _

lemma memLp_two_sq_gaussian_directional_score (m v k : EuclideanSpace ℝ ι)
    (N S : Matrix ι ι ℝ) :
    MemLp (fun x : EuclideanSpace ℝ ι ↦ (v ⬝ᵥ N⁻¹ *ᵥ (x - m)) ^ 2) 2
      (multivariateGaussian k S) := by
  have h := memLp_two_gaussianHeatQuadratic m k (Matrix.vecMulVec (v ᵥ* N⁻¹) (v ᵥ* N⁻¹)) S
  simp only [WithLp.ofLp_sub, quadratic_vecMulVec] at h
  simpa only [Matrix.dotProduct_mulVec] using h

lemma integrable_gaussian_lineDeriv_mul (m v : EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) (f : EuclideanSpace ℝ ι → ℝ)
    (hf : MemLp f 2 (multivariateGaussian m N)) :
    Integrable (fun x ↦ lineDeriv ℝ (multivariateGaussianPDFReal m N) x v * f x) volume := by
  have hp := (memLp_two_gaussian_directional_score m v m N N).neg.integrable_mul hf
  have hi := (integrable_multivariateGaussianPDFReal_mul_iff m N hN _).mpr hp
  simp_rw [(hasLineDerivAt_multivariateGaussianPDFReal m _ v N hN).lineDeriv]
  convert! hi using 1
  ext x
  simp only [Pi.mul_apply, Pi.neg_apply]
  ring

lemma integrable_gaussian_lineDeriv_lineDeriv_mul (m v : EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) (f : EuclideanSpace ℝ ι → ℝ)
    (hf : MemLp f 2 (multivariateGaussian m N)) :
    Integrable (fun x ↦ lineDeriv ℝ
      (fun y ↦ lineDeriv ℝ (multivariateGaussianPDFReal m N) y v) x v * f x) volume := by
  have hc : MemLp (fun _ : EuclideanSpace ℝ ι ↦ v ⬝ᵥ N⁻¹ *ᵥ v) 2
      (multivariateGaussian m N) := memLp_const _
  have hp := ((memLp_two_sq_gaussian_directional_score m v m N N).sub hc).integrable_mul hf
  have hi := (integrable_multivariateGaussianPDFReal_mul_iff m N hN _).mpr hp
  simp_rw [(hasLineDerivAt_lineDeriv_multivariateGaussianPDFReal m _ v N hN).lineDeriv]
  convert! hi using 1
  ext x
  simp only [Pi.mul_apply, Pi.sub_apply]
  ring

lemma integrable_gaussianMixture_lineDeriv_mul (w : α → ℝ)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (v : EuclideanSpace ℝ ι) (f : EuclideanSpace ℝ ι → ℝ)
    (hf : ∀ k, MemLp f 2 (multivariateGaussian (m k) N)) :
    Integrable (fun x ↦ lineDeriv ℝ (gaussianMixturePDFReal w m N) x v * f x) volume := by
  simp_rw [lineDeriv_gaussianMixturePDFReal_eq_sum w m N hN, Finset.sum_mul, mul_assoc]
  exact integrable_finsetSum _ (fun k _ ↦
    (integrable_gaussian_lineDeriv_mul (m k) v N hN f (hf k)).const_mul (w k))

lemma integrable_gaussianMixture_lineDeriv_lineDeriv_mul (w : α → ℝ)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (v : EuclideanSpace ℝ ι) (f : EuclideanSpace ℝ ι → ℝ)
    (hf : ∀ k, MemLp f 2 (multivariateGaussian (m k) N)) :
    Integrable (fun x ↦ lineDeriv ℝ
      (fun y ↦ lineDeriv ℝ (gaussianMixturePDFReal w m N) y v) x v * f x) volume := by
  unfold gaussianMixturePDFReal
  simp_rw [lineDeriv_lineDeriv_gaussian_mixture w m N hN, Finset.sum_mul, mul_assoc]
  exact integrable_finsetSum _ (fun k _ ↦
    (integrable_gaussian_lineDeriv_lineDeriv_mul (m k) v N hN f (hf k)).const_mul (w k))

lemma hasLineDerivAt_one_add_log_gaussianMixturePDFReal
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (x v : EuclideanSpace ℝ ι) :
    HasLineDerivAt ℝ (fun y ↦ 1 + log (gaussianMixturePDFReal w m N y))
      (lineDeriv ℝ (gaussianMixturePDFReal w m N) x v / gaussianMixturePDFReal w m N x) x v := by
  have hp := hasLineDerivAt_gaussianMixturePDFReal w m N hN x v
  have hpos := gaussianMixturePDFReal_pos w hw hw1 m N hN x
  unfold HasLineDerivAt at hp ⊢
  have hd := hp.log (by simpa only [zero_smul, add_zero] using hpos.ne')
  simpa only [zero_smul, add_zero] using hd.const_add 1

/-- Integration by parts identifies the entropy's directional second-derivative term. -/
theorem integral_one_add_log_mul_secondDeriv_gaussianMixture
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    {t : ℝ} (ht : 0 < t) (v : EuclideanSpace ℝ ι) :
    (∫ x, (1 + log (gaussianMixturePDFReal w m (t • N) x)) * lineDeriv ℝ
      (fun y ↦ lineDeriv ℝ (gaussianMixturePDFReal w m (t • N)) y v) x v) =
        -directionalFisherWith volume (gaussianMixturePDFReal w m (t • N)) v := by
  obtain ⟨j, _, hj⟩ := (Finset.sum_pos_iff_of_nonneg (fun a (_ : a ∈ Finset.univ) ↦ hw a)).mp
    (show 0 < ∑ a, w a by rw [hw1]; norm_num)
  have hlog (k : α) : MemLp (fun x ↦ 1 + log (gaussianMixturePDFReal w m (t • N) x)) 2
      (multivariateGaussian (m k) (t • N)) := by
    have hc : MemLp (fun _ : EuclideanSpace ℝ ι ↦ (1 : ℝ)) 2
        (multivariateGaussian (m k) (t • N)) := memLp_const 1
    exact hc.add (memLp_two_log_gaussianMixturePDFReal_smul w hw hw1 m N hN j hj ht
      (m k) (t • N))
  have hfisher : Integrable (fun x ↦
      (lineDeriv ℝ (gaussianMixturePDFReal w m (t • N)) x v /
        gaussianMixturePDFReal w m (t • N) x) *
          lineDeriv ℝ (gaussianMixturePDFReal w m (t • N)) x v) volume := by
    convert! integrable_fisher_gaussian_mixture w m (fun _ ↦ t • N) (fun _ ↦ hN.smul ht) v hw using 1
    ext x
    change _ = (lineDeriv ℝ (gaussianMixturePDFReal w m (t • N)) x v) ^ 2 /
      gaussianMixturePDFReal w m (t • N) x
    ring
  have hfirst := integrable_gaussianMixture_lineDeriv_mul w m (t • N) (hN.smul ht) v _ hlog
  have hsecond := integrable_gaussianMixture_lineDeriv_lineDeriv_mul w m (t • N) (hN.smul ht) v _ hlog
  have h := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℝ) (μ := volume) hfisher
    (by simpa only [ContinuousLinearMap.mul_apply', mul_comm] using hsecond)
    (by simpa only [ContinuousLinearMap.mul_apply', mul_comm] using hfirst)
    (fun x _ ↦ hasLineDerivAt_one_add_log_gaussianMixturePDFReal w hw hw1 m (t • N) (hN.smul ht) x v)
    (fun x _ ↦ hasLineDerivAt_lineDeriv_gaussianMixturePDFReal w m (t • N) (hN.smul ht) x v)
  convert! h using 1
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  simp only [ContinuousLinearMap.mul_apply']
  ring

lemma entropyWith_gaussianMixtureDensity (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hw1 : ∑ a, w a = 1) (m : α → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) :
    entropyWith (volume.withDensity (fun x ↦ ENNReal.ofReal (gaussianMixturePDFReal w m N x)))
      volume = -(∫ x, gaussianMixturePDFReal w m N x * log (gaussianMixturePDFReal w m N x)) := by
  have hmeas := (measurable_gaussianMixturePDFReal w m N).ennreal_ofReal
  rw [entropyWith, integral_congr_ae (llr_eq_log_density _ volume hmeas rfl),
    integral_withDensity_eq_integral_toReal_smul hmeas
      (Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (gaussianMixturePDFReal_pos w hw hw1 m N hN _).le,
    smul_eq_mul]

/-- The de Bruijn identity for native finite Gaussian mixtures with isotropic covariance. -/
theorem hasDerivAt_entropyWith_gaussianMixture_isotropic
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ entropyWith (volume.withDensity
      (fun x ↦ ENNReal.ofReal (gaussianMixturePDFReal w m (s • (1 : Matrix ι ι ℝ)) x))) volume)
      ((1 / 2 : ℝ) * ∑ i, directionalFisherWith volume
        (gaussianMixturePDFReal w m (t • (1 : Matrix ι ι ℝ))) (EuclideanSpace.single i 1)) t := by
  have hI : (1 : Matrix ι ι ℝ).PosDef := Matrix.PosDef.one
  obtain ⟨j, _, hj⟩ := (Finset.sum_pos_iff_of_nonneg (fun a (_ : a ∈ Finset.univ) ↦ hw a)).mp
    (show 0 < ∑ a, w a by rw [hw1]; norm_num)
  have hlog (k : α) : MemLp (fun x ↦ 1 +
      log (gaussianMixturePDFReal w m (t • (1 : Matrix ι ι ℝ)) x)) 2
        (multivariateGaussian (m k) (t • (1 : Matrix ι ι ℝ))) := by
    have hc : MemLp (fun _ : EuclideanSpace ℝ ι ↦ (1 : ℝ)) 2
        (multivariateGaussian (m k) (t • (1 : Matrix ι ι ℝ))) := memLp_const 1
    exact hc.add (memLp_two_log_gaussianMixturePDFReal_smul w hw hw1 m 1 hI j hj ht
      (m k) (t • (1 : Matrix ι ι ℝ)))
  have hheat (x : EuclideanSpace ℝ ι) : gaussianMixtureHeatDeriv w m 1 t x =
      (1 / 2 : ℝ) * ∑ i, lineDeriv ℝ (fun y ↦ lineDeriv ℝ
        (gaussianMixturePDFReal w m (t • (1 : Matrix ι ι ℝ))) y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1) :=
    (hasDerivAt_gaussianMixturePDFReal_smul w m 1 hI x ht).unique
      (hasDerivAt_gaussian_mixture_heat w m x ht)
  have hderiv := (hasDerivAt_integral_gaussianMixturePDFReal_mul_log w hw hw1 m 1 hI ht).neg
  have heq : (fun s ↦ entropyWith (volume.withDensity
      (fun x ↦ ENNReal.ofReal (gaussianMixturePDFReal w m (s • (1 : Matrix ι ι ℝ)) x))) volume)
      =ᶠ[𝓝 t] (fun s ↦ -(∫ x, gaussianMixturePDFReal w m (s • (1 : Matrix ι ι ℝ)) x *
        log (gaussianMixturePDFReal w m (s • (1 : Matrix ι ι ℝ)) x))) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact entropyWith_gaussianMixtureDensity w hw hw1 m (s • (1 : Matrix ι ι ℝ)) (hI.smul hs)
  apply (hderiv.congr_of_eventuallyEq heq).congr_deriv
  simp_rw [hheat, mul_assoc, Finset.sum_mul]
  rw [integral_const_mul, integral_finsetSum]
  · simp_rw [mul_comm (lineDeriv ℝ _ _ _),
      integral_one_add_log_mul_secondDeriv_gaussianMixture w hw hw1 m 1 hI ht]
    simp only [Finset.sum_neg_distrib]
    ring
  · intro i _
    exact integrable_gaussianMixture_lineDeriv_lineDeriv_mul w m
      (t • (1 : Matrix ι ι ℝ)) (hI.smul ht) (EuclideanSpace.single i 1) _ hlog

end CapacityAtlas.MeasureInformation
