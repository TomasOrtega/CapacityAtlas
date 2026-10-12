/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianDirtyPaper.Information
import CapacityAtlasForMathlib.InformationTheory.GaussianInformationDensity
import CapacityAtlasForMathlib.InformationTheory.GaussianRelativeEntropy

open MeasureTheory ProbabilityTheory Matrix Real CapacityAtlas.MeasureInformation
open scoped BigOperators ENNReal

namespace CapacityAtlas.Gaussian.DirtyPaper

variable {ι ο : Type*} [Fintype ι] [Fintype ο] [DecidableEq ι] [DecidableEq ο]

noncomputable def stateInformationDensity (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (s u : EuclideanSpace ℝ ι) : ℝ :=
  gaussianInformationDensity (costaCoefficient H Q N * H) Q 0 (auxiliaryCovariance H Q S N) s u

noncomputable def observationInformationDensity (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (y : EuclideanSpace ℝ ο) (u : EuclideanSpace ℝ ι) : ℝ :=
  gaussianInformationDensity (costaCoefficient H Q N) (residualCovariance H Q N) 0
    (auxiliaryCovariance H Q S N) y u

@[fun_prop]
theorem measurable_stateInformationDensity (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) :
    Measurable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦
      stateInformationDensity H Q S N p.1 p.2) := measurable_gaussianInformationDensity _ _ _ _

@[fun_prop]
theorem measurable_observationInformationDensity (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) :
    Measurable (fun p : EuclideanSpace ℝ ο × EuclideanSpace ℝ ι ↦
      observationInformationDensity H Q S N p.1 p.2) := measurable_gaussianInformationDensity _ _ _ _

theorem stateKernel_eq_withDensity (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosDef) (hS : S.PosSemidef) (s : EuclideanSpace ℝ ι) :
    gaussianChannel (costaCoefficient H Q N * H) Q s =
      (multivariateGaussian 0 (auxiliaryCovariance H Q S N)).withDensity
        (fun u ↦ ENNReal.ofReal (exp (stateInformationDensity H Q S N s u))) :=
  gaussianChannel_eq_withDensity_informationDensity _ Q hQ _ _
    (auxiliaryCovariance_posDef H Q S N hQ hS) s

theorem observationKernel_eq_withDensity (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosDef) (hS : S.PosSemidef) (hN : N.PosDef)
    (y : EuclideanSpace ℝ ο) :
    gaussianChannel (costaCoefficient H Q N) (residualCovariance H Q N) y =
      (multivariateGaussian 0 (auxiliaryCovariance H Q S N)).withDensity
        (fun u ↦ ENNReal.ofReal (exp (observationInformationDensity H Q S N y u))) :=
  gaussianChannel_eq_withDensity_informationDensity _ _ (residualCovariance_posDef H Q N hQ hN) _ _
    (auxiliaryCovariance_posDef H Q S N hQ hS) y

theorem memLp_two_stateInformationDensity (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosDef) (hS : S.PosSemidef) :
    MemLp (fun p ↦ stateInformationDensity H Q S N p.2 (auxiliary H Q N p)) 2
      (sourceLaw Q S N) := by
  have hjoint : HasGaussianLaw (fun p : SourceSpace ι ο ↦ (p.2, auxiliary H Q N p))
      (sourceLaw Q S N) := IsGaussian.hasGaussianLaw_id.map
        ((ContinuousLinearMap.snd ℝ _ _).prod (auxiliary H Q N))
  exact memLp_two_gaussianInformationDensity hjoint _ Q hQ _ _
    (auxiliaryCovariance_posDef H Q S N hQ hS)

theorem memLp_two_observationInformationDensity (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosDef) (hS : S.PosSemidef) (hN : N.PosDef) :
    MemLp (fun p ↦ observationInformationDensity H Q S N (observation H p) (auxiliary H Q N p)) 2
      (sourceLaw Q S N) := by
  have hjoint : HasGaussianLaw (fun p ↦ (observation H p, auxiliary H Q N p)) (sourceLaw Q S N) :=
    IsGaussian.hasGaussianLaw_id.map ((observation H).prod (auxiliary H Q N))
  exact memLp_two_gaussianInformationDensity hjoint _ _ (residualCovariance_posDef H Q N hQ hN) _ _
    (auxiliaryCovariance_posDef H Q S N hQ hS)

theorem integral_stateInformationDensity (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosDef) (hS : S.PosSemidef) :
    (∫ p, stateInformationDensity H Q S N p.2 (auxiliary H Q N p) ∂sourceLaw Q S N) =
      (mutualInfoRV (auxiliary H Q N) Prod.snd (sourceLaw Q S N)).toReal := by
  rw [mutualInfoRV_symm _ (by fun_prop) (by fun_prop), mutualInfoRV,
    sourceLaw_map_state_auxiliary]
  have hmap := integral_map (μ := sourceLaw Q S N)
    (by fun_prop : AEMeasurable (fun p : SourceSpace ι ο ↦ (p.2, auxiliary H Q N p)) _)
    (measurable_stateInformationDensity H Q S N).aestronglyMeasurable
  rw [sourceLaw_map_state_auxiliary] at hmap
  rw [← hmap]
  apply integral_gaussianInformationDensity _ Q hQ _ _ _ (auxiliaryCovariance_posDef H Q S N hQ hS)
  rw [state_channel_output_eq_auxiliary, sourceLaw_map_auxiliary H Q S N hQ.posSemidef hS]

theorem integral_observationInformationDensity (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosDef) (hS : S.PosSemidef) (hN : N.PosDef) :
    (∫ p, observationInformationDensity H Q S N (observation H p) (auxiliary H Q N p)
      ∂sourceLaw Q S N) =
      (mutualInfoRV (auxiliary H Q N) (observation H) (sourceLaw Q S N)).toReal := by
  rw [mutualInfoRV_symm _ (by fun_prop) (by fun_prop), mutualInfoRV,
    sourceLaw_map_observation_auxiliary H Q S N hQ.posSemidef hN]
  have hmap := integral_map (μ := sourceLaw Q S N)
    (by fun_prop : AEMeasurable (fun p ↦ (observation H p, auxiliary H Q N p)) _)
    (measurable_observationInformationDensity H Q S N).aestronglyMeasurable
  rw [sourceLaw_map_observation_auxiliary H Q S N hQ.posSemidef hN] at hmap
  rw [← hmap]
  apply integral_gaussianInformationDensity _ _ (residualCovariance_posDef H Q N hQ hN) _ _ _
    (auxiliaryCovariance_posDef H Q S N hQ hS)
  rw [regression_output_eq_auxiliary H Q S N hQ.posSemidef hN,
    sourceLaw_map_auxiliary H Q S N hQ.posSemidef hS]

noncomputable def encoderInput (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (s u : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  u - (costaCoefficient H Q N * H).toEuclideanLin s

noncomputable def inputCost (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (s u : EuclideanSpace ℝ ι) : ℝ := ‖encoderInput H Q N s u‖ ^ 2

theorem inputCost_nonneg (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (s u : EuclideanSpace ℝ ι) : 0 ≤ inputCost H Q N s u := sq_nonneg _

@[fun_prop]
theorem measurable_inputCost (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ) (N : Matrix ο ο ℝ) :
    Measurable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦ inputCost H Q N p.1 p.2) := by
  unfold inputCost encoderInput
  fun_prop

theorem inputCost_source (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ) (N : Matrix ο ο ℝ)
    (p : SourceSpace ι ο) : inputCost H Q N p.2 (auxiliary H Q N p) = ‖p.1.1‖ ^ 2 := by
  rw [inputCost, encoderInput, auxiliary_sub_state]

theorem memLp_two_inputCost (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ) (N : Matrix ο ο ℝ) :
    MemLp (fun p ↦ inputCost H Q N p.2 (auxiliary H Q N p)) 2 (sourceLaw Q S N) := by
  simp_rw [inputCost_source]
  have hX : HasGaussianLaw (fun p : SourceSpace ι ο ↦ p.1.1) (sourceLaw Q S N) :=
    IsGaussian.hasGaussianLaw_id.map
      ((ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ο)).comp
        (ContinuousLinearMap.fst ℝ (BaseSpace ι ο) (EuclideanSpace ℝ ι)))
  have h := memLp_two_covarianceQuadratic (fun p : SourceSpace ι ο ↦ p.1.1)
    (fun i ↦ (hX.map (EuclideanSpace.proj i)).memLp (by norm_num)) 0 (1 : Matrix ι ι ℝ)
  simp only [EuclideanSpace.real_norm_sq_eq]
  simpa [dotProduct, pow_two] using h

theorem integral_inputCost (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ) (N : Matrix ο ο ℝ)
    (hQ : Q.PosSemidef) :
    (∫ p, inputCost H Q N p.2 (auxiliary H Q N p) ∂sourceLaw Q S N) = Q.trace := by
  simp_rw [inputCost_source]
  have hmap := integral_map (μ := sourceLaw Q S N)
    (by fun_prop : AEMeasurable (fun p : SourceSpace ι ο ↦ p.1.1) _)
    (by fun_prop : AEStronglyMeasurable (fun x : EuclideanSpace ℝ ι ↦ ‖x‖ ^ 2) _)
  rw [sourceLaw_map_input] at hmap
  rw [← hmap]
  simp only [EuclideanSpace.real_norm_sq_eq]
  simpa [dotProduct, pow_two] using
    integral_quadratic_multivariateGaussian (0 : EuclideanSpace ℝ ι) 0 Q (1 : Matrix ι ι ℝ) hQ

noncomputable def physicalKernel (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ) (N : Matrix ο ο ℝ) :
    Kernel (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (EuclideanSpace ℝ ο) :=
  (gaussianChannel H N).comap (fun p ↦ encoderInput H Q N p.1 p.2 + p.1)
    (by unfold encoderInput; fun_prop)

instance physicalKernel_isMarkovKernel (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) : IsMarkovKernel (physicalKernel H Q N) := by
  unfold physicalKernel
  infer_instance

theorem physicalKernel_apply (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ) (N : Matrix ο ο ℝ)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    physicalKernel H Q N p = multivariateGaussian
      (H.toEuclideanLin (encoderInput H Q N p.1 p.2 + p.1)) N := by
  rw [physicalKernel, Kernel.comap_apply, gaussianChannel_apply]

theorem physicalKernel_compProd_eq_map (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (μ : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) [SFinite μ] :
    μ ⊗ₘ physicalKernel H Q N = (μ.prod (multivariateGaussian 0 N)).map
      (fun p ↦ (p.1, H.toEuclideanLin (encoderInput H Q N p.1.1 p.1.2 + p.1.1) + p.2)) := by
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply (by unfold encoderInput; fun_prop) hs,
    Measure.prod_apply ((by unfold encoderInput; fun_prop : Measurable
      (fun p : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) × EuclideanSpace ℝ ο ↦
        (p.1, H.toEuclideanLin (encoderInput H Q N p.1.1 p.1.2 + p.1.1) + p.2))) hs)]
  apply lintegral_congr
  intro p
  rw [physicalKernel, Kernel.comap_apply, gaussianChannel_apply_eq_map,
    Measure.map_apply (by fun_prop) (measurable_prodMk_left hs)]
  rfl

theorem sourceLaw_map_state_input_noise (Q S : Matrix ι ι ℝ) (N : Matrix ο ο ℝ) :
    (sourceLaw Q S N).map (fun p ↦ ((p.2, p.1.1), p.1.2)) =
      ((multivariateGaussian 0 S).prod (multivariateGaussian 0 Q)).prod (multivariateGaussian 0 N) := by
  have h := (MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (multivariateGaussian 0 S) (multivariateGaussian 0 Q)
      (multivariateGaussian 0 N))).comp
        (Measure.measurePreserving_swap (μ := baseLaw Q N) (ν := multivariateGaussian 0 S))
  exact h.map_eq

theorem sourceLaw_map_state_auxiliary_noise (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) :
    (sourceLaw Q S N).map (fun p ↦ ((p.2, auxiliary H Q N p), p.1.2)) =
      ((sourceLaw Q S N).map (fun p ↦ (p.2, auxiliary H Q N p))).prod (multivariateGaussian 0 N) := by
  let f : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι :=
    fun p ↦ (p.1, p.2 + (costaCoefficient H Q N * H).toEuclideanLin p.1)
  have hf : Measurable f := by unfold f; fun_prop
  have h := congrArg (fun ν ↦ ν.map (Prod.map f id)) (sourceLaw_map_state_input_noise Q S N)
  rw [Measure.map_map (hf.prodMap measurable_id) (by fun_prop),
    ← Measure.map_prod_map _ _ hf measurable_id, Measure.map_id] at h
  change (sourceLaw Q S N).map (fun p ↦ ((p.2, auxiliary H Q N p), p.1.2)) =
    (((multivariateGaussian 0 S).prod (multivariateGaussian 0 Q)).map f).prod
      (multivariateGaussian 0 N) at h
  have hfst := congrArg Measure.fst h
  rw [Measure.fst_map_prodMk (by fun_prop), Measure.fst_prod] at hfst
  simpa only [measure_univ, one_smul] using h.trans (congrArg
    (fun ν ↦ ν.prod (multivariateGaussian 0 N)) hfst).symm

theorem sourceLaw_map_physical_joint (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) :
    (sourceLaw Q S N).map (fun p ↦ ((p.2, auxiliary H Q N p), observation H p)) =
      ((sourceLaw Q S N).map (fun p ↦ (p.2, auxiliary H Q N p))) ⊗ₘ physicalKernel H Q N := by
  rw [physicalKernel_compProd_eq_map, ← sourceLaw_map_state_auxiliary_noise,
    Measure.map_map (by unfold encoderInput; fun_prop) (by fun_prop)]
  congr 1
  funext p
  change ((p.2, auxiliary H Q N p), observation H p) =
    ((p.2, auxiliary H Q N p),
      H.toEuclideanLin (encoderInput H Q N p.2 (auxiliary H Q N p) + p.2) + p.1.2)
  rw [encoderInput, auxiliary_sub_state, observation_apply]

theorem sourceLaw_map_physical_joint_native (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) :
    (sourceLaw Q S N).map (fun p ↦ ((p.2, auxiliary H Q N p), observation H p)) =
      (multivariateGaussian 0 S ⊗ₘ gaussianChannel (costaCoefficient H Q N * H) Q) ⊗ₘ
        physicalKernel H Q N := by
  rw [sourceLaw_map_physical_joint, sourceLaw_map_state_auxiliary]

theorem memLp_two_stateInformationDensity_joint (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosDef) (hS : S.PosSemidef) :
    MemLp (fun p ↦ stateInformationDensity H Q S N p.1 p.2) 2
      (multivariateGaussian 0 S ⊗ₘ gaussianChannel (costaCoefficient H Q N * H) Q) :=
  memLp_two_gaussianInformationDensity_joint _ Q hQ _ _ _ (auxiliaryCovariance_posDef H Q S N hQ hS)

theorem integral_stateInformationDensity_joint (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosDef) (hS : S.PosSemidef) :
    (∫ p, stateInformationDensity H Q S N p.1 p.2
      ∂(multivariateGaussian 0 S ⊗ₘ gaussianChannel (costaCoefficient H Q N * H) Q)) =
      (mutualInfoRV (auxiliary H Q N) Prod.snd (sourceLaw Q S N)).toReal := by
  rw [← sourceLaw_map_state_auxiliary H Q S N, integral_map (by fun_prop)
    (measurable_stateInformationDensity H Q S N).aestronglyMeasurable]
  exact integral_stateInformationDensity H Q S N hQ hS

theorem memLp_two_observationInformationDensity_physical
    (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ) (N : Matrix ο ο ℝ)
    (hQ : Q.PosDef) (hS : S.PosSemidef) (hN : N.PosDef) :
    MemLp (fun p ↦ observationInformationDensity H Q S N p.2 p.1.2) 2
      ((multivariateGaussian 0 S ⊗ₘ gaussianChannel (costaCoefficient H Q N * H) Q) ⊗ₘ
        physicalKernel H Q N) := by
  rw [← sourceLaw_map_physical_joint_native]
  apply (memLp_map_measure_iff
    ((measurable_observationInformationDensity H Q S N).comp
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).aestronglyMeasurable
    (by fun_prop)).mpr
  exact memLp_two_observationInformationDensity H Q S N hQ hS hN

theorem integral_observationInformationDensity_physical
    (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ) (N : Matrix ο ο ℝ)
    (hQ : Q.PosDef) (hS : S.PosSemidef) (hN : N.PosDef) :
    (∫ p, observationInformationDensity H Q S N p.2 p.1.2
      ∂((multivariateGaussian 0 S ⊗ₘ gaussianChannel (costaCoefficient H Q N * H) Q) ⊗ₘ
        physicalKernel H Q N)) =
      (mutualInfoRV (auxiliary H Q N) (observation H) (sourceLaw Q S N)).toReal := by
  have hf : Measurable (fun p : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) × EuclideanSpace ℝ ο ↦
      observationInformationDensity H Q S N p.2 p.1.2) := by
    simpa only [Function.comp_def] using (measurable_observationInformationDensity H Q S N).comp
      (by fun_prop : Measurable
        (fun p : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) × EuclideanSpace ℝ ο ↦ (p.2, p.1.2)))
  rw [← sourceLaw_map_physical_joint_native, integral_map (by fun_prop) hf.aestronglyMeasurable]
  exact integral_observationInformationDensity H Q S N hQ hS hN

theorem memLp_two_inputCost_joint (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ) (N : Matrix ο ο ℝ) :
    MemLp (fun p ↦ inputCost H Q N p.1 p.2) 2
      (multivariateGaussian 0 S ⊗ₘ gaussianChannel (costaCoefficient H Q N * H) Q) := by
  rw [← sourceLaw_map_state_auxiliary H Q S N]
  apply (memLp_map_measure_iff (by fun_prop) (by fun_prop)).mpr
  exact memLp_two_inputCost H Q S N

theorem integral_inputCost_joint (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ) (N : Matrix ο ο ℝ)
    (hQ : Q.PosSemidef) :
    (∫ p, inputCost H Q N p.1 p.2
      ∂(multivariateGaussian 0 S ⊗ₘ gaussianChannel (costaCoefficient H Q N * H) Q)) = Q.trace := by
  rw [← sourceLaw_map_state_auxiliary H Q S N, integral_map (by fun_prop) (by fun_prop)]
  exact integral_inputCost H Q S N hQ

end CapacityAtlas.Gaussian.DirtyPaper
