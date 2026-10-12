/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Probability.GaussianDensity
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp

open MeasureTheory Matrix
open scoped BigOperators ENNReal ProbabilityTheory RealInnerProductSpace

namespace ProbabilityTheory

variable {ι ο : Type*} [Fintype ι] [Fintype ο] [DecidableEq ι] [DecidableEq ο]

theorem multivariateGaussian_map_const_add (m c : EuclideanSpace ℝ ο)
    (N : Matrix ο ο ℝ) :
    (multivariateGaussian m N).map (fun y ↦ c + y) = multivariateGaussian (c + m) N := by
  rw [multivariateGaussian, multivariateGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  ext x
  simp only [Function.comp_apply, add_assoc]

/-- A rectangular real linear channel with independent native Gaussian noise. -/
noncomputable def gaussianChannel (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ) :
    Kernel (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ο) :=
  ((Kernel.deterministic (fun x ↦ H.toEuclideanLin x) (by fun_prop)) ×ₖ
    Kernel.const (EuclideanSpace ℝ ι) (multivariateGaussian 0 N)).map (fun p ↦ p.1 + p.2)

instance gaussianChannel_isMarkovKernel (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ) :
    IsMarkovKernel (gaussianChannel H N) := by
  unfold gaussianChannel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

theorem gaussianChannel_apply_eq_map (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (x : EuclideanSpace ℝ ι) :
    gaussianChannel H N x = (multivariateGaussian 0 N).map (fun z ↦ H.toEuclideanLin x + z) := by
  rw [gaussianChannel, Kernel.map_apply _ (by fun_prop), Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem gaussianChannel_apply (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (x : EuclideanSpace ℝ ι) :
    gaussianChannel H N x = multivariateGaussian (H.toEuclideanLin x) N := by
  rw [gaussianChannel_apply_eq_map, multivariateGaussian_map_const_add, add_zero]

theorem gaussianChannel_apply_eq_withDensity (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (hN : N.PosDef) (x : EuclideanSpace ℝ ι) :
    gaussianChannel H N x = volume.withDensity
      (fun y ↦ ENNReal.ofReal (multivariateGaussianPDFReal (H.toEuclideanLin x) N y)) := by
  rw [gaussianChannel_apply, multivariateGaussian_eq_withDensity _ N hN]

@[fun_prop]
theorem measurable_gaussianChannel_density (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ) :
    Measurable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ο ↦
      multivariateGaussianPDFReal (H.toEuclideanLin p.1) N p.2) := by
  unfold multivariateGaussianPDFReal dotProduct Matrix.mulVec
  fun_prop

theorem gaussianChannel_density_pos (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (hN : N.PosDef) (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ ο) :
    0 < multivariateGaussianPDFReal (H.toEuclideanLin x) N y :=
  multivariateGaussianPDFReal_pos _ N hN y

theorem gaussianChannel_absolutelyContinuous (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (hN : N.PosDef) (x : EuclideanSpace ℝ ι) :
    gaussianChannel H N x ≪ volume := by
  rw [gaussianChannel_apply]
  exact multivariateGaussian_absolutelyContinuous _ N hN

theorem gaussianChannel_compProd_eq_withDensity (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (hN : N.PosDef) (μ : Measure (EuclideanSpace ℝ ι)) [SFinite μ] :
    μ ⊗ₘ gaussianChannel H N = (μ.prod volume).withDensity
      (fun p ↦ ENNReal.ofReal (multivariateGaussianPDFReal (H.toEuclideanLin p.1) N p.2)) := by
  ext s hs
  rw [Measure.compProd_apply hs, withDensity_apply _ hs, ← lintegral_indicator hs,
    lintegral_prod _
      ((measurable_gaussianChannel_density H N).ennreal_ofReal.indicator hs).aemeasurable]
  apply lintegral_congr
  intro x
  rw [gaussianChannel_apply_eq_withDensity H N hN,
    withDensity_apply _ (measurable_prodMk_left hs),
    ← lintegral_indicator (measurable_prodMk_left hs)]
  rfl

theorem gaussianChannel_compProd_absolutelyContinuous (H : Matrix ο ι ℝ)
    (N : Matrix ο ο ℝ) (hN : N.PosDef)
    (μ : Measure (EuclideanSpace ℝ ι)) [SFinite μ] :
    μ ⊗ₘ gaussianChannel H N ≪ μ.prod volume := by
  rw [gaussianChannel_compProd_eq_withDensity H N hN]
  exact withDensity_absolutelyContinuous _ _

theorem rnDeriv_gaussianChannel_compProd (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (hN : N.PosDef) (μ : Measure (EuclideanSpace ℝ ι)) [SigmaFinite μ] :
    (μ ⊗ₘ gaussianChannel H N).rnDeriv (μ.prod volume) =ᵐ[μ.prod volume]
      fun p ↦ ENNReal.ofReal (multivariateGaussianPDFReal (H.toEuclideanLin p.1) N p.2) := by
  rw [gaussianChannel_compProd_eq_withDensity H N hN]
  exact Measure.rnDeriv_withDensity _ (measurable_gaussianChannel_density H N).ennreal_ofReal

theorem llr_gaussianChannel_compProd (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (hN : N.PosDef) (μ : Measure (EuclideanSpace ℝ ι)) [SigmaFinite μ] :
    llr (μ ⊗ₘ gaussianChannel H N) (μ.prod volume) =ᵐ[μ ⊗ₘ gaussianChannel H N]
      fun p ↦ Real.log (multivariateGaussianPDFReal (H.toEuclideanLin p.1) N p.2) := by
  filter_upwards [(gaussianChannel_compProd_absolutelyContinuous H N hN μ).ae_le
    (rnDeriv_gaussianChannel_compProd H N hN μ)] with p hp
  simp only [llr, hp,
    ENNReal.toReal_ofReal (multivariateGaussianPDFReal_pos _ N hN _).le]

theorem inner_toEuclideanLin_transpose (H : Matrix ο ι ℝ)
    (x : EuclideanSpace ℝ ι) (t : EuclideanSpace ℝ ο) :
    ⟪H.toEuclideanLin x, t⟫ = ⟪x, H.transpose.toEuclideanLin t⟫ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  change t.ofLp ⬝ᵥ H *ᵥ x.ofLp = (H.transpose *ᵥ t.ofLp) ⬝ᵥ x.ofLp
  rw [dotProduct_comm (H.transpose *ᵥ t.ofLp)]
  exact (Matrix.dotProduct_transpose_mulVec H x.ofLp t.ofLp).symm

theorem charFun_map_matrix (H : Matrix ο ι ℝ) (μ : Measure (EuclideanSpace ℝ ι))
    (t : EuclideanSpace ℝ ο) :
    charFun (μ.map (fun x ↦ H.toEuclideanLin x)) t =
      charFun μ (H.transpose.toEuclideanLin t) := by
  rw [charFun_apply, charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [inner_toEuclideanLin_transpose]

omit [DecidableEq ι] in
theorem quadratic_toEuclideanLin_transpose (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (t : EuclideanSpace ℝ ο) :
    (H.transpose.toEuclideanLin t) ⬝ᵥ Q *ᵥ (H.transpose.toEuclideanLin t) =
      t ⬝ᵥ (H * Q * H.transpose) *ᵥ t := by
  change (H.transpose *ᵥ t.ofLp) ⬝ᵥ Q *ᵥ (H.transpose *ᵥ t.ofLp) = _
  rw [dotProduct_comm (H.transpose *ᵥ t.ofLp), Matrix.dotProduct_transpose_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem multivariateGaussian_map_matrix (H : Matrix ο ι ℝ)
    (m : EuclideanSpace ℝ ι) (Q : Matrix ι ι ℝ) (hQ : Q.PosSemidef) :
    (multivariateGaussian m Q).map (fun x ↦ H.toEuclideanLin x) =
      multivariateGaussian (H.toEuclideanLin m) (H * Q * H.transpose) := by
  have hHQ : (H * Q * H.transpose).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hQ.mul_mul_conjTranspose_same H
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_map_matrix, charFun_multivariateGaussian hQ,
    charFun_multivariateGaussian hHQ, quadratic_toEuclideanLin_transpose]
  congr 2
  rw [inner_toEuclideanLin_transpose, transpose_transpose]

theorem multivariateGaussian_conv (m n : EuclideanSpace ℝ ο) (Q N : Matrix ο ο ℝ)
    (hQ : Q.PosSemidef) (hN : N.PosSemidef) :
    multivariateGaussian m Q ∗ multivariateGaussian n N =
      multivariateGaussian (m + n) (Q + N) := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_conv, charFun_multivariateGaussian hQ, charFun_multivariateGaussian hN,
    charFun_multivariateGaussian (hQ.add hN), ← Complex.exp_add]
  congr 1
  simp only [inner_add_right, Matrix.add_mulVec, dotProduct_add, Complex.ofReal_add]
  ring

theorem gaussianChannel_comp_eq_map (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (μ : Measure (EuclideanSpace ℝ ι)) [SFinite μ] :
    gaussianChannel H N ∘ₘ μ =
      (μ.prod (multivariateGaussian 0 N)).map (fun p ↦ H.toEuclideanLin p.1 + p.2) := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), Measure.map_apply (by fun_prop) hs,
    Measure.prod_apply ((by fun_prop : Measurable
      (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ο ↦ H.toEuclideanLin p.1 + p.2)) hs)]
  apply lintegral_congr
  intro x
  rw [gaussianChannel_apply_eq_map, Measure.map_apply (by fun_prop) hs]
  rfl

theorem gaussianChannel_compProd_eq_map (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (μ : Measure (EuclideanSpace ℝ ι)) [SFinite μ] :
    μ ⊗ₘ gaussianChannel H N = (μ.prod (multivariateGaussian 0 N)).map
      (fun p ↦ (p.1, H.toEuclideanLin p.1 + p.2)) := by
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply (by fun_prop) hs,
    Measure.prod_apply ((by fun_prop : Measurable
      (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ο ↦
        (p.1, H.toEuclideanLin p.1 + p.2))) hs)]
  apply lintegral_congr
  intro x
  rw [gaussianChannel_apply_eq_map,
    Measure.map_apply (by fun_prop) (measurable_prodMk_left hs)]
  rfl

theorem gaussianChannel_comp_eq_conv (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (μ : Measure (EuclideanSpace ℝ ι)) [SFinite μ] :
    gaussianChannel H N ∘ₘ μ =
      μ.map (fun x ↦ H.toEuclideanLin x) ∗ multivariateGaussian 0 N := by
  rw [gaussianChannel_comp_eq_map, Measure.conv]
  conv_rhs => rw [← Measure.map_id (μ := multivariateGaussian 0 N)]
  rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem gaussianChannel_comp_multivariateGaussian (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (hN : N.PosSemidef) (m : EuclideanSpace ℝ ι) (Q : Matrix ι ι ℝ)
    (hQ : Q.PosSemidef) :
    gaussianChannel H N ∘ₘ multivariateGaussian m Q =
      multivariateGaussian (H.toEuclideanLin m) (N + H * Q * H.transpose) := by
  have hHQ : (H * Q * H.transpose).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hQ.mul_mul_conjTranspose_same H
  rw [gaussianChannel_comp_eq_conv, multivariateGaussian_map_matrix H m Q hQ,
    multivariateGaussian_conv _ _ _ _ hHQ hN, add_zero, add_comm N]

theorem gaussianChannel_compProd_isGaussian (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsGaussian μ] :
    IsGaussian (μ ⊗ₘ gaussianChannel H N) := by
  rw [gaussianChannel_compProd_eq_map]
  let fst := ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ο)
  let snd := ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ο)
  let L := fst.prod ((H.toEuclideanLin.toContinuousLinearMap).comp fst + snd)
  change IsGaussian ((μ.prod (multivariateGaussian 0 N)).map L)
  infer_instance

omit [DecidableEq ι] [DecidableEq ο] in
theorem gaussianChannel_output_covariance_posDef (H : Matrix ο ι ℝ)
    (N : Matrix ο ο ℝ) (hN : N.PosDef) (Q : Matrix ι ι ℝ) (hQ : Q.PosSemidef) :
    (N + H * Q * H.transpose).PosDef := by
  apply hN.add_posSemidef
  simpa only [conjTranspose_eq_transpose_of_trivial] using hQ.mul_mul_conjTranspose_same H

theorem covariance_gaussianChannel_output (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (hN : N.PosSemidef) (m : EuclideanSpace ℝ ι) (Q : Matrix ι ι ℝ)
    (hQ : Q.PosSemidef) (i j : ο) :
    cov[fun x ↦ x i, fun x ↦ x j; gaussianChannel H N ∘ₘ multivariateGaussian m Q] =
      (N + H * Q * H.transpose) i j := by
  rw [gaussianChannel_comp_multivariateGaussian H N hN m Q hQ]
  apply covariance_eval_multivariateGaussian
  apply hN.add
  simpa only [conjTranspose_eq_transpose_of_trivial] using hQ.mul_mul_conjTranspose_same H

theorem gaussianChannel_output_eq_withDensity (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (hN : N.PosDef) (m : EuclideanSpace ℝ ι) (Q : Matrix ι ι ℝ)
    (hQ : Q.PosSemidef) :
    gaussianChannel H N ∘ₘ multivariateGaussian m Q = volume.withDensity
      (fun y ↦ ENNReal.ofReal (multivariateGaussianPDFReal
        (H.toEuclideanLin m) (N + H * Q * H.transpose) y)) := by
  rw [gaussianChannel_comp_multivariateGaussian H N hN.posSemidef m Q hQ]
  exact multivariateGaussian_eq_withDensity _ _
    (gaussianChannel_output_covariance_posDef H N hN Q hQ)

end ProbabilityTheory
