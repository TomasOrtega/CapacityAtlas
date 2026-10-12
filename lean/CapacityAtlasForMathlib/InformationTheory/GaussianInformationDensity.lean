/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianChannelEntropy
import CapacityAtlasForMathlib.Probability.GaussianRegression

open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal

namespace CapacityAtlas.MeasureInformation

variable {Ω ι ο : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype ο]

theorem memLp_two_covarianceQuadratic {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : Ω → EuclideanSpace ℝ ι) (hX : ∀ i, MemLp (fun ω ↦ X ω i) 4 μ)
    (m : EuclideanSpace ℝ ι) (A : Matrix ι ι ℝ) :
    MemLp (fun ω ↦ (X ω - m) ⬝ᵥ A *ᵥ (X ω - m)) 2 μ := by
  letI : ENNReal.HolderTriple 4 4 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add]⟩
  simp_rw [covarianceQuadratic_eq_sum]
  apply memLp_finsetSum
  intro i _
  apply memLp_finsetSum
  intro j _
  exact (((hX j).sub (memLp_const (m j))).mul'
    ((hX i).sub (memLp_const (m i)))).const_mul _

theorem memLp_two_log_multivariateGaussianPDFReal [DecidableEq ι]
    {μ : Measure Ω} {X : Ω → EuclideanSpace ℝ ι} (hX : HasGaussianLaw X μ)
    (m : EuclideanSpace ℝ ι) (C : Matrix ι ι ℝ) (hC : C.PosDef) :
    MemLp (fun ω ↦ log (multivariateGaussianPDFReal m C (X ω))) 2 μ := by
  have := hX.isProbabilityMeasure
  have hquad := memLp_two_covarianceQuadratic X
    (fun i ↦ (hX.map (EuclideanSpace.proj i)).memLp (by norm_num)) m C⁻¹
  simp_rw [log_multivariateGaussianPDFReal m C hC]
  simpa only [div_eq_mul_inv, Pi.sub_def] using (memLp_const _).sub (hquad.mul_const 2⁻¹)

variable [DecidableEq ι] [DecidableEq ο]

noncomputable def gaussianInformationDensity (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (m : EuclideanSpace ℝ ο) (C : Matrix ο ο ℝ)
    (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ ο) : ℝ :=
  log (multivariateGaussianPDFReal (H.toEuclideanLin x) N y) -
    log (multivariateGaussianPDFReal m C y)

@[fun_prop]
theorem measurable_gaussianInformationDensity (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (m : EuclideanSpace ℝ ο) (C : Matrix ο ο ℝ) :
    Measurable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ο ↦
      gaussianInformationDensity H N m C p.1 p.2) :=
  (measurable_gaussianChannel_density H N).log.sub
    (((measurable_multivariateGaussianPDFReal m C).comp measurable_snd).log)

theorem exp_gaussianInformationDensity (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (hN : N.PosDef) (m : EuclideanSpace ℝ ο) (C : Matrix ο ο ℝ) (hC : C.PosDef)
    (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ ο) :
    exp (gaussianInformationDensity H N m C x y) =
      multivariateGaussianPDFReal (H.toEuclideanLin x) N y / multivariateGaussianPDFReal m C y := by
  rw [gaussianInformationDensity, exp_sub,
    exp_log (multivariateGaussianPDFReal_pos _ N hN _),
    exp_log (multivariateGaussianPDFReal_pos m C hC _)]

theorem multivariateGaussian_absolutelyContinuous_multivariateGaussian
    (m : EuclideanSpace ℝ ο) (N : Matrix ο ο ℝ) (hN : N.PosDef)
    (n : EuclideanSpace ℝ ο) (C : Matrix ο ο ℝ) (hC : C.PosDef) :
    multivariateGaussian m N ≪ multivariateGaussian n C := by
  rw [multivariateGaussian_eq_withDensity n C hC]
  apply absolutelyContinuous_withDensity_of_ae_ne_zero
    (multivariateGaussian_absolutelyContinuous m N hN)
    (measurable_multivariateGaussianPDFReal n C).ennreal_ofReal
  exact Filter.Eventually.of_forall fun y ↦
    (ENNReal.ofReal_pos.mpr (multivariateGaussianPDFReal_pos n C hC y)).ne'

theorem rnDeriv_gaussianChannel_gaussian (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (hN : N.PosDef) (m : EuclideanSpace ℝ ο) (C : Matrix ο ο ℝ) (hC : C.PosDef)
    (x : EuclideanSpace ℝ ι) :
    (gaussianChannel H N x).rnDeriv (multivariateGaussian m C) =ᵐ[multivariateGaussian m C]
      fun y ↦ ENNReal.ofReal (exp (gaussianInformationDensity H N m C x y)) := by
  rw [gaussianChannel_apply]
  have hac := multivariateGaussian_absolutelyContinuous m C hC
  filter_upwards [Measure.rnDeriv_eq_div
    (multivariateGaussian_absolutelyContinuous (H.toEuclideanLin x) N hN) hac,
    hac.ae_le (rnDeriv_multivariateGaussian_volume (H.toEuclideanLin x) N hN),
    hac.ae_le (rnDeriv_multivariateGaussian_volume m C hC)] with y hy hp hq
  rw [hy, hp, hq, exp_gaussianInformationDensity H N hN m C hC,
    ENNReal.ofReal_div_of_pos (multivariateGaussianPDFReal_pos m C hC y)]

theorem gaussianChannel_eq_withDensity_informationDensity
    (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ) (hN : N.PosDef)
    (m : EuclideanSpace ℝ ο) (C : Matrix ο ο ℝ) (hC : C.PosDef)
    (x : EuclideanSpace ℝ ι) :
    gaussianChannel H N x = (multivariateGaussian m C).withDensity
      (fun y ↦ ENNReal.ofReal (exp (gaussianInformationDensity H N m C x y))) := by
  rw [← Measure.withDensity_rnDeriv_eq (gaussianChannel H N x) (multivariateGaussian m C)
    (by rw [gaussianChannel_apply]
        exact multivariateGaussian_absolutelyContinuous_multivariateGaussian _ N hN m C hC)]
  exact withDensity_congr_ae (rnDeriv_gaussianChannel_gaussian H N hN m C hC x)

theorem lintegral_exp_gaussianInformationDensity
    (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ) (hN : N.PosDef)
    (m : EuclideanSpace ℝ ο) (C : Matrix ο ο ℝ) (hC : C.PosDef)
    (x : EuclideanSpace ℝ ι) :
    (∫⁻ y, ENNReal.ofReal (exp (gaussianInformationDensity H N m C x y))
      ∂multivariateGaussian m C) = 1 := by
  have h := congrArg (fun ν : Measure (EuclideanSpace ℝ ο) ↦ ν Set.univ)
    (gaussianChannel_eq_withDensity_informationDensity H N hN m C hC x)
  simpa only [measure_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] using h.symm

theorem llr_gaussianChannel_gaussian (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (hN : N.PosDef) (m : EuclideanSpace ℝ ο) (C : Matrix ο ο ℝ) (hC : C.PosDef)
    (x : EuclideanSpace ℝ ι) :
    llr (gaussianChannel H N x) (multivariateGaussian m C) =ᵐ[gaussianChannel H N x]
      gaussianInformationDensity H N m C x := by
  have hac : gaussianChannel H N x ≪ multivariateGaussian m C := by
    rw [gaussianChannel_apply]
    exact multivariateGaussian_absolutelyContinuous_multivariateGaussian _ N hN m C hC
  filter_upwards [hac.ae_le (rnDeriv_gaussianChannel_gaussian H N hN m C hC x)] with y hy
  simp only [llr, hy, ENNReal.toReal_ofReal (exp_pos _).le, log_exp]

theorem gaussianChannel_density_eq_residual (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ ο) :
    multivariateGaussianPDFReal (H.toEuclideanLin x) N y =
      multivariateGaussianPDFReal 0 N (y - H.toEuclideanLin x) := by
  simp [multivariateGaussianPDFReal, WithLp.ofLp_sub]

theorem memLp_two_gaussianInformationDensity
    {μ : Measure Ω} {X : Ω → EuclideanSpace ℝ ι} {Y : Ω → EuclideanSpace ℝ ο}
    (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) μ)
    (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ) (hN : N.PosDef)
    (m : EuclideanSpace ℝ ο) (C : Matrix ο ο ℝ) (hC : C.PosDef) :
    MemLp (fun ω ↦ gaussianInformationDensity H N m C (X ω) (Y ω)) 2 μ := by
  let L : EuclideanSpace ℝ ι × EuclideanSpace ℝ ο →L[ℝ] EuclideanSpace ℝ ο :=
    .snd ℝ _ _ - H.toEuclideanLin.toContinuousLinearMap.comp (.fst ℝ _ _)
  have hres : HasGaussianLaw (fun ω ↦ Y ω - H.toEuclideanLin (X ω)) μ := hXY.map L
  have hrow := memLp_two_log_multivariateGaussianPDFReal hres 0 N hN
  have hout := memLp_two_log_multivariateGaussianPDFReal hXY.snd m C hC
  simpa only [gaussianInformationDensity, gaussianChannel_density_eq_residual, Pi.sub_def]
    using hrow.sub hout

theorem memLp_two_gaussianInformationDensity_joint
    (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ) (hN : N.PosDef)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsGaussian μ]
    (m : EuclideanSpace ℝ ο) (C : Matrix ο ο ℝ) (hC : C.PosDef) :
    MemLp (fun p ↦ gaussianInformationDensity H N m C p.1 p.2) 2
      (μ ⊗ₘ gaussianChannel H N) := by
  letI := gaussianChannel_compProd_isGaussian H N μ
  exact memLp_two_gaussianInformationDensity IsGaussian.hasGaussianLaw_id H N hN m C hC

theorem llr_joint_eq_gaussianInformationDensity
    (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ) (hN : N.PosDef)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (m : EuclideanSpace ℝ ο) (C : Matrix ο ο ℝ) (hC : C.PosDef)
    (hout : gaussianChannel H N ∘ₘ μ = multivariateGaussian m C) :
    llr (μ ⊗ₘ gaussianChannel H N) (μ.prod (gaussianChannel H N ∘ₘ μ)) =ᵐ[μ ⊗ₘ gaussianChannel H N]
      fun p ↦ gaussianInformationDensity H N m C p.1 p.2 := by
  have h := llr_mutualInfo_eq_sub (μ ⊗ₘ gaussianChannel H N) volume
    (by simpa only [Measure.fst_compProd] using
      gaussianChannel_compProd_absolutelyContinuous H N hN μ)
  simp only [Measure.fst_compProd, Measure.snd_compProd] at h
  have hy : llr (μ ⊗ₘ gaussianChannel H N).snd volume =ᵐ[(μ ⊗ₘ gaussianChannel H N).snd]
      fun y ↦ log (multivariateGaussianPDFReal m C y) := by
    rw [Measure.snd_compProd, hout]
    exact llr_multivariateGaussian_volume m C hC
  have hp := ae_of_ae_map measurable_snd.aemeasurable hy
  simp only [Measure.snd_compProd] at hp
  filter_upwards [h, llr_gaussianChannel_compProd H N hN μ, hp] with p h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  rfl

theorem integral_gaussianInformationDensity
    (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ) (hN : N.PosDef)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (m : EuclideanSpace ℝ ο) (C : Matrix ο ο ℝ) (hC : C.PosDef)
    (hout : gaussianChannel H N ∘ₘ μ = multivariateGaussian m C) :
    (∫ p, gaussianInformationDensity H N m C p.1 p.2 ∂(μ ⊗ₘ gaussianChannel H N)) =
      (mutualInfo (μ ⊗ₘ gaussianChannel H N)).toReal := by
  have houtlog : Integrable (llr (gaussianChannel H N ∘ₘ μ) volume) (gaussianChannel H N ∘ₘ μ) := by
    rw [hout]
    exact integrable_llr_multivariateGaussian_volume m C hC
  have hfinite := mutualInfo_gaussianChannel_ne_top H N hN μ houtlog
  have hspec := _root_.InformationTheory.klDiv_ne_top_iff.mp hfinite
  rw [mutualInfo, _root_.InformationTheory.toReal_klDiv hspec.1 hspec.2]
  simp only [Measure.fst_compProd, Measure.snd_compProd, probReal_univ, add_sub_cancel_right]
  exact integral_congr_ae (llr_joint_eq_gaussianInformationDensity H N hN μ m C hC hout).symm

theorem integral_gaussianInformationDensity_native
    (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ) (hN : N.PosDef)
    (m : EuclideanSpace ℝ ι) (Q : Matrix ι ι ℝ) (hQ : Q.PosSemidef) :
    (∫ p, gaussianInformationDensity H N (H.toEuclideanLin m)
        (N + H * Q * H.transpose) p.1 p.2
      ∂(multivariateGaussian m Q ⊗ₘ gaussianChannel H N)) =
      log ((N + H * Q * H.transpose).det / N.det) / 2 := by
  rw [integral_gaussianInformationDensity H N hN _ _ _
    (gaussianChannel_output_covariance_posDef H N hN Q hQ)
    (gaussianChannel_comp_multivariateGaussian H N hN.posSemidef m Q hQ),
    mutualInfo_gaussianChannel_gaussian_eq_log_det_ratio H N hN m Q hQ]

end CapacityAtlas.MeasureInformation
