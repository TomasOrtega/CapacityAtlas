/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianDirtyPaper.Covariance
import CapacityAtlasForMathlib.InformationTheory.GaussianChannelEntropy
import CapacityAtlasForMathlib.Probability.GaussianRegression

open MeasureTheory ProbabilityTheory Matrix CapacityAtlas.MeasureInformation
open scoped BigOperators

namespace CapacityAtlas.Gaussian.DirtyPaper

variable {ι ο : Type*} [Fintype ι] [Fintype ο] [DecidableEq ι] [DecidableEq ο]

abbrev BaseSpace (ι ο : Type*) := EuclideanSpace ℝ ι × EuclideanSpace ℝ ο
abbrev SourceSpace (ι ο : Type*) := BaseSpace ι ο × EuclideanSpace ℝ ι

noncomputable def baseLaw (Q : Matrix ι ι ℝ) (N : Matrix ο ο ℝ) : Measure (BaseSpace ι ο) :=
  (multivariateGaussian 0 Q).prod (multivariateGaussian 0 N)

noncomputable def sourceLaw (Q S : Matrix ι ι ℝ) (N : Matrix ο ο ℝ) :
    Measure (SourceSpace ι ο) := (baseLaw Q N).prod (multivariateGaussian 0 S)

instance baseLaw_isGaussian (Q : Matrix ι ι ℝ) (N : Matrix ο ο ℝ) : IsGaussian (baseLaw Q N) := by
  unfold baseLaw
  infer_instance

instance sourceLaw_isGaussian (Q S : Matrix ι ι ℝ) (N : Matrix ο ο ℝ) :
    IsGaussian (sourceLaw Q S N) := by
  unfold sourceLaw
  infer_instance

noncomputable def baseOutput (H : Matrix ο ι ℝ) : BaseSpace ι ο →L[ℝ] EuclideanSpace ℝ ο :=
  matrixPair H 1

noncomputable def baseResidual (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ) (N : Matrix ο ο ℝ) :
    BaseSpace ι ο →L[ℝ] EuclideanSpace ℝ ι :=
  matrixPair (1 - costaCoefficient H Q N * H) (-costaCoefficient H Q N)

noncomputable def observation (H : Matrix ο ι ℝ) : SourceSpace ι ο →L[ℝ] EuclideanSpace ℝ ο :=
  (baseOutput H).comp (.fst ℝ _ _) +
    (H.toEuclideanLin.toContinuousLinearMap).comp (.snd ℝ _ _)

noncomputable def auxiliary (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ) (N : Matrix ο ο ℝ) :
    SourceSpace ι ο →L[ℝ] EuclideanSpace ℝ ι :=
  (ContinuousLinearMap.fst ℝ _ _).comp (.fst ℝ _ _) +
    ((costaCoefficient H Q N * H).toEuclideanLin.toContinuousLinearMap).comp (.snd ℝ _ _)

noncomputable def residual (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ) (N : Matrix ο ο ℝ) :
    SourceSpace ι ο →L[ℝ] EuclideanSpace ℝ ι :=
  (baseResidual H Q N).comp (.fst ℝ _ _)

@[simp]
theorem baseOutput_apply (H : Matrix ο ι ℝ) (p : BaseSpace ι ο) :
    baseOutput H p = H.toEuclideanLin p.1 + p.2 := by
  simp [baseOutput, Matrix.toEuclideanLin]

@[simp]
theorem observation_apply (H : Matrix ο ι ℝ) (p : SourceSpace ι ο) :
    observation H p = H.toEuclideanLin (p.1.1 + p.2) + p.1.2 := by
  change baseOutput H p.1 + H.toEuclideanLin p.2 = _
  rw [baseOutput_apply, map_add]
  abel

@[simp]
theorem auxiliary_apply (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ) (N : Matrix ο ο ℝ)
    (p : SourceSpace ι ο) :
    auxiliary H Q N p = p.1.1 + (costaCoefficient H Q N * H).toEuclideanLin p.2 := rfl

theorem auxiliary_eq_regression (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (p : SourceSpace ι ο) :
    auxiliary H Q N p = (costaCoefficient H Q N).toEuclideanLin (observation H p) +
      residual H Q N p := by
  simp [auxiliary, observation, residual, baseOutput, baseResidual, matrixPair,
    Matrix.toEuclideanLin, map_sub, map_neg, map_add]
  abel

theorem baseLaw_map_output (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ) (N : Matrix ο ο ℝ)
    (hQ : Q.PosSemidef) (hN : N.PosSemidef) :
    (baseLaw Q N).map (baseOutput H) = multivariateGaussian 0 (outputCovariance H Q N) := by
  change ((multivariateGaussian 0 Q).prod (multivariateGaussian 0 N)).map
    (fun p ↦ H.toEuclideanLin p.1 + (1 : Matrix ο ο ℝ).toEuclideanLin p.2) = _
  simpa [outputCovariance, add_comm] using
    multivariateGaussian_map_prod_add H (1 : Matrix ο ο ℝ) 0 0 Q N hQ hN

theorem baseLaw_map_residual (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ) (N : Matrix ο ο ℝ)
    (hQ : Q.PosSemidef) (hN : N.PosDef) :
    (baseLaw Q N).map (baseResidual H Q N) =
      multivariateGaussian 0 (residualCovariance H Q N) := by
  rw [residualCovariance_eq_independent H Q N hQ hN]
  change ((multivariateGaussian 0 Q).prod (multivariateGaussian 0 N)).map
    (fun p ↦ (1 - costaCoefficient H Q N * H).toEuclideanLin p.1 +
      (-costaCoefficient H Q N).toEuclideanLin p.2) = _
  simpa only [map_zero, add_zero, Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg,
    neg_neg] using
    multivariateGaussian_map_prod_add (1 - costaCoefficient H Q N * H)
      (-costaCoefficient H Q N) 0 0 Q N hQ hN.posSemidef

theorem baseResidual_output_covariance_zero (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosSemidef) (hN : N.PosDef) (a : ι) (b : ο) :
    cov[fun p ↦ baseResidual H Q N p a, fun p ↦ baseOutput H p b; baseLaw Q N] = 0 := by
  have h := covariance_gaussian_prod_matrix 0 0 Q N hQ hN.posSemidef
    (1 - costaCoefficient H Q N * H) (-costaCoefficient H Q N) H
    (1 : Matrix ο ο ℝ) a b
  calc
    _ = (((1 - costaCoefficient H Q N * H) * Q * H.transpose -
      costaCoefficient H Q N * N) : Matrix ι ο ℝ) a b := by
      simpa [baseLaw, baseResidual, baseOutput, matrixPair_apply, ← sub_eq_add_neg] using h
    _ = 0 := by rw [residualCrossCovariance_zero H Q N hQ hN]; rfl

theorem sourceLaw_map_state (Q S : Matrix ι ι ℝ) (N : Matrix ο ο ℝ) :
    (sourceLaw Q S N).map Prod.snd = multivariateGaussian 0 S := by
  simp [sourceLaw]

theorem sourceLaw_map_input (Q S : Matrix ι ι ℝ) (N : Matrix ο ο ℝ) :
    (sourceLaw Q S N).map (fun p ↦ p.1.1) = multivariateGaussian 0 Q := by
  change ((baseLaw Q N).prod (multivariateGaussian 0 S)).map (Prod.fst ∘ Prod.fst) = _
  rw [← Measure.map_map measurable_fst measurable_fst]
  simp [baseLaw]

theorem sourceLaw_map_residual (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ) (N : Matrix ο ο ℝ)
    (hQ : Q.PosSemidef) (hN : N.PosDef) :
    (sourceLaw Q S N).map (residual H Q N) = multivariateGaussian 0 (residualCovariance H Q N) := by
  change ((baseLaw Q N).prod (multivariateGaussian 0 S)).map ((baseResidual H Q N) ∘ Prod.fst) = _
  rw [← Measure.map_map (by fun_prop) measurable_fst]
  simpa using baseLaw_map_residual H Q N hQ hN

theorem residual_observation_covariance_zero (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosSemidef) (hN : N.PosDef) (a : ι) (b : ο) :
    cov[fun p ↦ residual H Q N p a, fun p ↦ observation H p b; sourceLaw Q S N] = 0 := by
  have hR : MemLp (fun p ↦ baseResidual H Q N p a) 2 (baseLaw Q N) :=
    (IsGaussian.hasGaussianLaw_id.map ((EuclideanSpace.proj a).comp (baseResidual H Q N))).memLp_two
  have hY : MemLp (fun p ↦ baseOutput H p b) 2 (baseLaw Q N) :=
    (IsGaussian.hasGaussianLaw_id.map ((EuclideanSpace.proj b).comp (baseOutput H))).memLp_two
  have h := covariance_prod_add hR hY
    (memLp_const (μ := multivariateGaussian 0 S) (p := 2) (0 : ℝ))
    (memLp_matrix_multivariateGaussian 0 S H b)
  change cov[fun p : SourceSpace ι ο ↦ baseResidual H Q N p.1 a,
    fun p : SourceSpace ι ο ↦ baseOutput H p.1 b + (H.toEuclideanLin p.2) b;
    (baseLaw Q N).prod (multivariateGaussian 0 S)] = _
  simpa only [add_zero, covariance_const_left,
    baseResidual_output_covariance_zero H Q N hQ hN, zero_add] using h

theorem residual_indep_observation (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosSemidef) (hN : N.PosDef) :
    IndepFun (residual H Q N) (observation H) (sourceLaw Q S N) := by
  have hjoint : HasGaussianLaw (fun p ↦ (residual H Q N p, observation H p)) (sourceLaw Q S N) :=
    IsGaussian.hasGaussianLaw_id.map ((residual H Q N).prod (observation H))
  exact hjoint.indepFun_of_covariance_euclidean
    (residual_observation_covariance_zero H Q S N hQ hN)

theorem sourceLaw_map_observation_auxiliary (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosSemidef) (hN : N.PosDef) :
    (sourceLaw Q S N).map (fun p ↦ (observation H p, auxiliary H Q N p)) =
      (sourceLaw Q S N).map (observation H) ⊗ₘ
        gaussianChannel (costaCoefficient H Q N) (residualCovariance H Q N) := by
  have h := (residual_indep_observation H Q S N hQ hN).symm.map_add_eq_compProd_gaussianChannel
    (by fun_prop) (by fun_prop) (costaCoefficient H Q N) (residualCovariance H Q N)
    (sourceLaw_map_residual H Q S N hQ hN)
  simpa only [auxiliary_eq_regression] using h

theorem sourceLaw_map_state_auxiliary (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) :
    (sourceLaw Q S N).map (fun p ↦ (p.2, auxiliary H Q N p)) =
      multivariateGaussian 0 S ⊗ₘ gaussianChannel (costaCoefficient H Q N * H) Q := by
  have hind : IndepFun (fun p : SourceSpace ι ο ↦ p.2) (fun p ↦ p.1.1) (sourceLaw Q S N) :=
    (indepFun_prod (μ := baseLaw Q N) (ν := multivariateGaussian 0 S)
      measurable_fst measurable_id).symm
  have h := hind.map_add_eq_compProd_gaussianChannel (by fun_prop) (by fun_prop)
    (costaCoefficient H Q N * H) Q (sourceLaw_map_input Q S N)
  simpa only [sourceLaw_map_state, auxiliary_apply, add_comm] using h

noncomputable def auxiliaryCovariance (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) : Matrix ι ι ℝ :=
  Q + (costaCoefficient H Q N * H) * S * (costaCoefficient H Q N * H).transpose

omit [DecidableEq ι] in
theorem auxiliaryCovariance_posDef (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosDef) (hS : S.PosSemidef) :
    (auxiliaryCovariance H Q S N).PosDef :=
  gaussianChannel_output_covariance_posDef _ Q hQ S hS

theorem sourceLaw_map_auxiliary (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosSemidef) (hS : S.PosSemidef) :
    (sourceLaw Q S N).map (auxiliary H Q N) =
      multivariateGaussian 0 (auxiliaryCovariance H Q S N) := by
  have h := congrArg Measure.snd (sourceLaw_map_state_auxiliary H Q S N)
  rw [Measure.snd_map_prodMk (by fun_prop), Measure.snd_compProd,
    gaussianChannel_comp_multivariateGaussian _ Q hQ 0 S hS] at h
  simpa only [map_zero, auxiliaryCovariance] using h

theorem regression_output_eq_auxiliary (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosSemidef) (hN : N.PosDef) :
    gaussianChannel (costaCoefficient H Q N) (residualCovariance H Q N) ∘ₘ
      (sourceLaw Q S N).map (observation H) = (sourceLaw Q S N).map (auxiliary H Q N) := by
  have h := congrArg Measure.snd (sourceLaw_map_observation_auxiliary H Q S N hQ hN)
  rw [Measure.snd_map_prodMk (by fun_prop), Measure.snd_compProd] at h
  exact h.symm

theorem state_channel_output_eq_auxiliary (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) :
    gaussianChannel (costaCoefficient H Q N * H) Q ∘ₘ multivariateGaussian 0 S =
      (sourceLaw Q S N).map (auxiliary H Q N) := by
  have h := congrArg Measure.snd (sourceLaw_map_state_auxiliary H Q S N)
  rw [Measure.snd_map_prodMk (by fun_prop), Measure.snd_compProd] at h
  exact h.symm

theorem integrable_llr_auxiliary (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosDef) (hS : S.PosSemidef) :
    Integrable (llr ((sourceLaw Q S N).map (auxiliary H Q N)) volume)
      ((sourceLaw Q S N).map (auxiliary H Q N)) := by
  rw [sourceLaw_map_auxiliary H Q S N hQ.posSemidef hS]
  exact integrable_llr_multivariateGaussian_volume 0 _ (auxiliaryCovariance_posDef H Q S N hQ hS)

theorem auxiliary_observation_mutualInfo_ne_top (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosDef) (hS : S.PosSemidef) (hN : N.PosDef) :
    mutualInfoRV (auxiliary H Q N) (observation H) (sourceLaw Q S N) ≠ ⊤ := by
  rw [mutualInfoRV_symm _ (by fun_prop) (by fun_prop), mutualInfoRV,
    sourceLaw_map_observation_auxiliary H Q S N hQ.posSemidef hN]
  apply mutualInfo_gaussianChannel_ne_top _ _ (residualCovariance_posDef H Q N hQ hN)
  rw [regression_output_eq_auxiliary H Q S N hQ.posSemidef hN]
  exact integrable_llr_auxiliary H Q S N hQ hS

theorem auxiliary_state_mutualInfo_ne_top (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosDef) (hS : S.PosSemidef) :
    mutualInfoRV (auxiliary H Q N) Prod.snd (sourceLaw Q S N) ≠ ⊤ := by
  rw [mutualInfoRV_symm _ (by fun_prop) (by fun_prop), mutualInfoRV,
    sourceLaw_map_state_auxiliary]
  exact mutualInfo_gaussianChannel_gaussian_ne_top _ Q hQ 0 S hS

theorem auxiliary_observation_mutualInfo (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosDef) (hS : S.PosSemidef) (hN : N.PosDef) :
    (mutualInfoRV (auxiliary H Q N) (observation H) (sourceLaw Q S N)).toReal =
      entropyWith ((sourceLaw Q S N).map (auxiliary H Q N)) volume -
        entropyWith (multivariateGaussian 0 (residualCovariance H Q N)) volume := by
  rw [mutualInfoRV_symm _ (by fun_prop) (by fun_prop), mutualInfoRV,
    sourceLaw_map_observation_auxiliary H Q S N hQ.posSemidef hN]
  have hout : Integrable
      (llr (gaussianChannel (costaCoefficient H Q N) (residualCovariance H Q N) ∘ₘ
        (sourceLaw Q S N).map (observation H)) volume)
      (gaussianChannel (costaCoefficient H Q N) (residualCovariance H Q N) ∘ₘ
        (sourceLaw Q S N).map (observation H)) := by
    rw [regression_output_eq_auxiliary H Q S N hQ.posSemidef hN]
    exact integrable_llr_auxiliary H Q S N hQ hS
  rw [mutualInfo_gaussianChannel_eq_entropy_sub _ _
    (residualCovariance_posDef H Q N hQ hN) _ hout,
    regression_output_eq_auxiliary H Q S N hQ.posSemidef hN]

theorem auxiliary_state_mutualInfo (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosDef) (hS : S.PosSemidef) :
    (mutualInfoRV (auxiliary H Q N) Prod.snd (sourceLaw Q S N)).toReal =
      entropyWith ((sourceLaw Q S N).map (auxiliary H Q N)) volume -
        entropyWith (multivariateGaussian 0 Q) volume := by
  rw [mutualInfoRV_symm _ (by fun_prop) (by fun_prop), mutualInfoRV,
    sourceLaw_map_state_auxiliary]
  rw [mutualInfo_gaussianChannel_eq_entropy_sub _ Q hQ _
    (integrable_llr_gaussianChannel_output _ Q hQ 0 S hS),
    state_channel_output_eq_auxiliary]

/-- Costa's information difference for actual independent native Gaussian input, state, and noise. -/
theorem costa_information_difference (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosDef) (hS : S.PosSemidef) (hN : N.PosDef) :
    (mutualInfoRV (auxiliary H Q N) (observation H) (sourceLaw Q S N)).toReal -
      (mutualInfoRV (auxiliary H Q N) Prod.snd (sourceLaw Q S N)).toReal =
        (Real.log (outputCovariance H Q N).det - Real.log N.det) / 2 := by
  rw [auxiliary_observation_mutualInfo H Q S N hQ hS hN,
    auxiliary_state_mutualInfo H Q S N hQ hS,
    entropyWith_multivariateGaussian 0 Q hQ,
    entropyWith_multivariateGaussian 0 _ (residualCovariance_posDef H Q N hQ hN)]
  have h := log_det_residualCovariance H Q N hQ hN
  linarith

theorem costa_information_difference_log_det_ratio
    (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ) (N : Matrix ο ο ℝ)
    (hQ : Q.PosDef) (hS : S.PosSemidef) (hN : N.PosDef) :
    (mutualInfoRV (auxiliary H Q N) (observation H) (sourceLaw Q S N)).toReal -
      (mutualInfoRV (auxiliary H Q N) Prod.snd (sourceLaw Q S N)).toReal =
        Real.log ((outputCovariance H Q N).det / N.det) / 2 := by
  rw [costa_information_difference H Q S N hQ hS hN,
    Real.log_div (outputCovariance_posDef H Q N hQ.posSemidef hN).det_pos.ne' hN.det_pos.ne']

theorem costa_information_difference_eq_gaussianChannel
    (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ) (N : Matrix ο ο ℝ)
    (hQ : Q.PosDef) (hS : S.PosSemidef) (hN : N.PosDef) :
    (mutualInfoRV (auxiliary H Q N) (observation H) (sourceLaw Q S N)).toReal -
      (mutualInfoRV (auxiliary H Q N) Prod.snd (sourceLaw Q S N)).toReal =
        (mutualInfo (multivariateGaussian 0 Q ⊗ₘ gaussianChannel H N)).toReal := by
  rw [costa_information_difference H Q S N hQ hS hN,
    mutualInfo_gaussianChannel_gaussian H N hN 0 Q hQ.posSemidef]
  rfl

theorem auxiliary_sub_state (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (p : SourceSpace ι ο) :
    auxiliary H Q N p - (costaCoefficient H Q N * H).toEuclideanLin p.2 = p.1.1 := by
  rw [auxiliary_apply, add_sub_cancel_right]

end CapacityAtlas.Gaussian.DirtyPaper
