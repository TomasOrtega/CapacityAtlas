/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.ConditionalDifferentialEntropy
import CapacityAtlasForMathlib.InformationTheory.GaussianRelativeEntropy

open MeasureTheory ProbabilityTheory InformationTheory Real Matrix
open scoped ENNReal

namespace CapacityAtlas.MeasureInformation

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Fintype α] [MeasurableSingletonClass α]

/-- Finitely many integrable rows give an integrable mixture. -/
theorem integrable_comp_of_finite (μ : Measure α) [IsFiniteMeasure μ]
    (κ : Kernel α β) {f : β → ℝ} (hf : Measurable f)
    (hrows : ∀ a, Integrable f (κ a)) : Integrable f (κ ∘ₘ μ) := by
  exact (Measure.integrable_comp_iff hf.aestronglyMeasurable).mpr
    ⟨Filter.Eventually.of_forall hrows, Integrable.of_finite⟩

theorem klDiv_compProd_ne_top_of_finite (μ : Measure α) [IsProbabilityMeasure μ]
    (κ : Kernel α β) [IsMarkovKernel κ] (ν : Measure β) [IsProbabilityMeasure ν]
    (hrows : ∀ a, klDiv (κ a) ν ≠ ⊤) : klDiv (μ ⊗ₘ κ) (μ.prod ν) ≠ ⊤ := by
  let f : α × β → ℝ≥0∞ := fun p ↦ (κ p.1).rnDeriv ν p.2
  have hf : Measurable f :=
    measurable_from_prod_countable_right (fun a ↦ (κ a).measurable_rnDeriv ν)
  have hdensity (a : α) : κ a = ν.withDensity (fun b ↦ f (a, b)) :=
    (Measure.withDensity_rnDeriv_eq (κ a) ν (klDiv_ne_top_iff.mp (hrows a)).1).symm
  have hlog : Integrable (fun p ↦ log (f p).toReal) (μ ⊗ₘ κ) := by
    apply (Measure.integrable_compProd_iff hf.ennreal_toReal.log.aestronglyMeasurable).mpr
    exact ⟨Filter.Eventually.of_forall (fun a ↦ (klDiv_ne_top_iff.mp (hrows a)).2),
      Integrable.of_finite⟩
  have heq := compProd_eq_withDensity_of_rows μ κ ν hf hdensity
  apply klDiv_ne_top_iff.mpr
  constructor
  · rw [heq]
    exact withDensity_absolutelyContinuous _ _
  · exact hlog.congr (llr_eq_log_density _ _ hf heq).symm

/-- A finite mixture of finite-relative-entropy rows has finite relative entropy. -/
theorem klDiv_comp_ne_top_of_finite (μ : Measure α) [IsProbabilityMeasure μ]
    (κ : Kernel α β) [IsMarkovKernel κ] (ν : Measure β) [IsProbabilityMeasure ν]
    (hrows : ∀ a, klDiv (κ a) ν ≠ ⊤) : klDiv (κ ∘ₘ μ) ν ≠ ⊤ := by
  have hle := klDiv_snd_le (μ ⊗ₘ κ) (μ.prod ν)
  simp only [Measure.snd_compProd, Measure.snd_prod] at hle
  exact ne_top_of_le_ne_top (klDiv_compProd_ne_top_of_finite μ κ ν hrows) hle

omit [Fintype α] [MeasurableSingletonClass α] in
theorem integral_comp_eq_integral (μ : Measure α) [IsFiniteMeasure μ]
    (κ : Kernel α β) [IsMarkovKernel κ] {f : β → ℝ}
    (hf : Integrable f (κ ∘ₘ μ)) :
    (∫ y, f y ∂κ ∘ₘ μ) = ∫ a, ∫ y, f y ∂κ a ∂μ := by
  have hpull := (Measure.integrable_compProd_snd_iff hf.aestronglyMeasurable).mpr hf
  calc
    (∫ y, f y ∂κ ∘ₘ μ) = ∫ p : α × β, f p.2 ∂μ ⊗ₘ κ := by
      conv_lhs => rw [← Measure.snd_compProd μ κ]
      exact integral_map measurable_snd.aemeasurable (by
        change AEStronglyMeasurable f (μ ⊗ₘ κ).snd
        simpa only [Measure.snd_compProd] using hf.aestronglyMeasurable)
    _ = ∫ a, ∫ y, f y ∂κ a ∂μ := Measure.integral_compProd hpull

/-- Every finite family of real random variables has a positive semidefinite covariance matrix. -/
theorem covarianceMatrix_posSemidef {ι : Type*} [Fintype ι]
    (μ : Measure α) [IsProbabilityMeasure μ] (X : ι → α → ℝ) :
    (Matrix.of fun i j ↦ covariance (X i) (X j) μ).PosSemidef := by
  classical
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · apply isHermitian_iff_isSymm.mpr
    ext i j
    simpa only [Matrix.transpose_apply, Matrix.of_apply] using covariance_comm (X j) (X i)
  · intro v
    let f : α → ℝ := fun a ↦ ∑ i, v i * X i a
    have hnonneg : 0 ≤ covariance f f μ := integral_nonneg (fun _ ↦ mul_self_nonneg _)
    have heq : covariance f f μ =
        v ⬝ᵥ (Matrix.of fun i j ↦ covariance (X i) (X j) μ) *ᵥ v := by
      dsimp only [f]
      rw [covariance_fun_sum_left (fun _ ↦ MemLp.of_discrete) MemLp.of_discrete]
      simp_rw [covariance_fun_sum_right (fun _ ↦ MemLp.of_discrete) MemLp.of_discrete,
        covariance_const_mul_left, covariance_const_mul_right]
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.of_apply]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    simpa only [star_trivial, ← heq] using hnonneg

section GaussianRows

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  (μ : Measure α) [IsProbabilityMeasure μ]
  (κ : Kernel α (EuclideanSpace ℝ ι)) [IsMarkovKernel κ]
  (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
  (hrows : ∀ a, κ a = multivariateGaussian (m a) N)

include hrows

omit [IsMarkovKernel κ] in
theorem memLp_eval_gaussianMixture (i : ι) :
    MemLp (fun y : EuclideanSpace ℝ ι ↦ y i) 2 (κ ∘ₘ μ) := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  apply integrable_comp_of_finite μ κ (by fun_prop)
  intro a
  rw [hrows a]
  exact (memLp_eval_multivariateGaussian (m a) N i).integrable_sq

include hN

omit [Fintype α] [MeasurableSingletonClass α] [IsMarkovKernel κ] in
theorem gaussianMixture_absolutelyContinuous : κ ∘ₘ μ ≪ volume := by
  have h := Measure.AbsolutelyContinuous.comp_left μ
    (κ := κ) (η := Kernel.const α (volume : Measure (EuclideanSpace ℝ ι)))
    (Filter.Eventually.of_forall (fun a ↦ by
      simpa only [Kernel.const_apply, hrows a] using
        multivariateGaussian_absolutelyContinuous (m a) N hN))
  simpa using h

theorem klDiv_gaussianMixture_ne_top (a : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) (hS : S.PosDef) :
    klDiv (κ ∘ₘ μ) (multivariateGaussian a S) ≠ ⊤ := by
  apply klDiv_comp_ne_top_of_finite μ κ
  intro x
  rw [hrows x]
  exact klDiv_multivariateGaussian_ne_top (m x) a N S hN hS

/-- Finite Gaussian codebooks always have an integrable output log density. -/
theorem integrable_llr_gaussianMixture_volume :
    Integrable (llr (κ ∘ₘ μ) volume) (κ ∘ₘ μ) := by
  let γ : Measure (EuclideanSpace ℝ ι) := multivariateGaussian 0 (1 : Matrix ι ι ℝ)
  have hI : (1 : Matrix ι ι ℝ).PosDef := Matrix.PosDef.one
  have hfin := klDiv_gaussianMixture_ne_top μ κ m N hN hrows 0 1 hI
  have hspec := klDiv_ne_top_iff.mp hfin
  have hγ : γ ≪ volume := multivariateGaussian_absolutelyContinuous 0 1 hI
  have hlog : Integrable (llr γ volume) (κ ∘ₘ μ) := by
    apply (integrable_log_multivariateGaussianPDFReal 0 1 hI
      (integrable_covarianceQuadratic (memLp_eval_gaussianMixture μ κ m N hrows) 0 1⁻¹)).congr
    exact hspec.1.ae_le (llr_multivariateGaussian_volume 0 1 hI).symm
  have hchain := llr_sub_of_absolutelyContinuous (μ := κ ∘ₘ μ) (τ := γ) hspec.1 hγ
  apply (hspec.2.add hlog).congr
  filter_upwards [hchain] with y hy
  change llr (κ ∘ₘ μ) γ y + llr γ volume y = _
  linarith

private theorem gaussianMixture_density_facts :
    let f : α × EuclideanSpace ℝ ι → ℝ≥0∞ :=
      fun p ↦ ENNReal.ofReal (multivariateGaussianPDFReal (m p.1) N p.2)
    Measurable f ∧ (∀ a, κ a = volume.withDensity (fun b ↦ f (a, b))) ∧
      Integrable (fun p ↦ log (f p).toReal) (μ ⊗ₘ κ) := by
  dsimp only
  have hf : Measurable (fun p : α × EuclideanSpace ℝ ι ↦
      ENNReal.ofReal (multivariateGaussianPDFReal (m p.1) N p.2)) :=
    measurable_from_prod_countable_right (fun a ↦
      (measurable_multivariateGaussianPDFReal (m a) N).ennreal_ofReal)
  refine ⟨hf, ?_, ?_⟩
  · intro a
    rw [hrows a]
    exact multivariateGaussian_eq_withDensity (m a) N hN
  · apply (Measure.integrable_compProd_iff hf.ennreal_toReal.log.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall (fun a ↦ ?_), Integrable.of_finite⟩
    simp only [ENNReal.toReal_ofReal (multivariateGaussianPDFReal_pos _ N hN _).le, hrows a]
    exact integrable_log_multivariateGaussianPDFReal (m a) N hN
      (integrable_covarianceQuadratic_multivariateGaussian (m a) N hN)

theorem mutualInfo_gaussianMixture_ne_top : mutualInfo (μ ⊗ₘ κ) ≠ ⊤ := by
  obtain ⟨hf, hden, hlog⟩ := gaussianMixture_density_facts μ κ m N hN hrows
  exact mutualInfo_compProd_ne_top μ κ volume hf hden hlog
    (integrable_llr_gaussianMixture_volume μ κ m N hN hrows)

theorem mutualInfo_gaussianMixture_eq_entropy_sub :
    (mutualInfo (μ ⊗ₘ κ)).toReal = entropyWith (κ ∘ₘ μ) volume -
      entropyWith (multivariateGaussian 0 N) volume := by
  obtain ⟨hf, hden, hlog⟩ := gaussianMixture_density_facts μ κ m N hN hrows
  rw [mutualInfo_compProd_eq_entropy_sub_integral μ κ volume hf hden hlog
    (integrable_llr_gaussianMixture_volume μ κ m N hN hrows)]
  simp_rw [hrows, entropyWith_multivariateGaussian _ N hN]
  simp

/-- A finite Gaussian codebook is bounded by the Gaussian with its actual output covariance. -/
theorem mutualInfo_gaussianMixture_le_of_covariance
    (a : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (hS : S.PosDef)
    (hmean : ∀ i, (∫ y : EuclideanSpace ℝ ι, y i ∂κ ∘ₘ μ) = a i)
    (hcov : ∀ i j, covariance (fun y : EuclideanSpace ℝ ι ↦ y i)
      (fun y ↦ y j) (κ ∘ₘ μ) = S i j) :
    (mutualInfo (μ ⊗ₘ κ)).toReal ≤ (log S.det - log N.det) / 2 := by
  have h := entropyWith_le_multivariateGaussian_of_covariance
    (gaussianMixture_absolutelyContinuous μ κ m N hN hrows)
    (integrable_llr_gaussianMixture_volume μ κ m N hN hrows)
    (memLp_eval_gaussianMixture μ κ m N hrows) a S hS hmean hcov
  rw [mutualInfo_gaussianMixture_eq_entropy_sub μ κ m N hN hrows,
    entropyWith_multivariateGaussian 0 N hN]
  rw [entropyWith_multivariateGaussian a S hS] at h
  linarith

theorem mutualInfo_gaussianMixture_le_of_covariance_ennreal
    (a : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (hS : S.PosDef)
    (hmean : ∀ i, (∫ y : EuclideanSpace ℝ ι, y i ∂κ ∘ₘ μ) = a i)
    (hcov : ∀ i j, covariance (fun y : EuclideanSpace ℝ ι ↦ y i)
      (fun y ↦ y j) (κ ∘ₘ μ) = S i j) :
    mutualInfo (μ ⊗ₘ κ) ≤ ENNReal.ofReal ((log S.det - log N.det) / 2) := by
  rw [← ENNReal.ofReal_toReal (mutualInfo_gaussianMixture_ne_top μ κ m N hN hrows)]
  exact ENNReal.ofReal_le_ofReal
    (mutualInfo_gaussianMixture_le_of_covariance μ κ m N hN hrows a S hS hmean hcov)

omit hN in
theorem integral_eval_gaussianMixture (i : ι) :
    (∫ y : EuclideanSpace ℝ ι, y i ∂κ ∘ₘ μ) = ∫ a, m a i ∂μ := by
  rw [integral_comp_eq_integral μ κ
    ((memLp_eval_gaussianMixture μ κ m N hrows i).integrable (by simp))]
  simp_rw [hrows, integral_eval_multivariateGaussian]

theorem covariance_eval_gaussianMixture (i j : ι) :
    covariance (fun y : EuclideanSpace ℝ ι ↦ y i) (fun y ↦ y j) (κ ∘ₘ μ) =
      N i j + covariance (fun a ↦ m a i) (fun a ↦ m a j) μ := by
  have hsecond (a : α) : (∫ y : EuclideanSpace ℝ ι, y i * y j ∂κ a) =
      N i j + m a i * m a j := by
    rw [hrows a]
    have h := covariance_eq_sub (memLp_eval_multivariateGaussian (m a) N i)
      (memLp_eval_multivariateGaussian (m a) N j)
    rw [covariance_eval_multivariateGaussian hN.posSemidef,
      integral_eval_multivariateGaussian, integral_eval_multivariateGaussian] at h
    change N i j = (∫ y, y i * y j ∂multivariateGaussian (m a) N) - m a i * m a j at h
    linarith
  rw [covariance_eq_sub (memLp_eval_gaussianMixture μ κ m N hrows i)
    (memLp_eval_gaussianMixture μ κ m N hrows j)]
  rw [integral_eval_gaussianMixture μ κ m N hrows,
    integral_eval_gaussianMixture μ κ m N hrows]
  rw [integral_comp_eq_integral μ κ
    ((memLp_eval_gaussianMixture μ κ m N hrows i).integrable_mul
      (memLp_eval_gaussianMixture μ κ m N hrows j))]
  simp_rw [Pi.mul_apply, hsecond]
  rw [integral_add (integrable_const _) Integrable.of_finite,
    covariance_eq_sub (MemLp.of_discrete) (MemLp.of_discrete)]
  simp only [integral_const, probReal_univ, one_smul, Pi.mul_apply]
  ring

omit hrows [IsMarkovKernel κ] [DecidableEq ι] in
theorem gaussianMixture_covariance_posDef :
    (N + Matrix.of (fun i j ↦ covariance (fun a ↦ m a i) (fun a ↦ m a j) μ)).PosDef :=
  hN.add_posSemidef (covarianceMatrix_posSemidef μ (fun i a ↦ m a i))

/-- An explicit finite-codebook converse with the covariance of its row means. -/
theorem mutualInfo_gaussianMixture_le :
    (mutualInfo (μ ⊗ₘ κ)).toReal ≤
      (log (N + Matrix.of (fun i j ↦ covariance (fun a ↦ m a i) (fun a ↦ m a j) μ)).det -
        log N.det) / 2 := by
  apply mutualInfo_gaussianMixture_le_of_covariance μ κ m N hN hrows
    (WithLp.toLp 2 (fun i ↦ ∫ a, m a i ∂μ)) _
    (gaussianMixture_covariance_posDef μ m N hN)
  · exact integral_eval_gaussianMixture μ κ m N hrows
  · exact covariance_eval_gaussianMixture μ κ m N hN hrows

theorem mutualInfo_gaussianMixture_le_ennreal :
    mutualInfo (μ ⊗ₘ κ) ≤ ENNReal.ofReal
      ((log (N + Matrix.of (fun i j ↦ covariance (fun a ↦ m a i) (fun a ↦ m a j) μ)).det -
        log N.det) / 2) := by
  rw [← ENNReal.ofReal_toReal (mutualInfo_gaussianMixture_ne_top μ κ m N hN hrows)]
  exact ENNReal.ofReal_le_ofReal (mutualInfo_gaussianMixture_le μ κ m N hN hrows)

end GaussianRows

end CapacityAtlas.MeasureInformation
