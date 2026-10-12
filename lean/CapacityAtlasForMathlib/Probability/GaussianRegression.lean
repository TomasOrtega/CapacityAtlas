/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Probability.GaussianChannel
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

open MeasureTheory Matrix
open scoped BigOperators ProbabilityTheory RealInnerProductSpace

namespace ProbabilityTheory

variable {Ω ι κ ο τ : Type*} [MeasurableSpace Ω]
  [Fintype ι] [Fintype κ] [Fintype ο] [Fintype τ]

omit [Fintype ο] [Fintype τ] in
theorem covariance_matrix_mulVec (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ι → ℝ) (hX : ∀ i, MemLp (fun ω ↦ X ω i) 2 μ)
    (A : Matrix ο ι ℝ) (D : Matrix τ ι ℝ) (a : ο) (b : τ) :
    cov[fun ω ↦ (A *ᵥ X ω) a, fun ω ↦ (D *ᵥ X ω) b; μ] =
      (A * (show Matrix ι ι ℝ from
        fun i j ↦ cov[fun ω ↦ X ω i, fun ω ↦ X ω j; μ]) * D.transpose) a b := by
  simp only [mulVec, dotProduct]
  rw [covariance_fun_sum_fun_sum (fun i ↦ (hX i).const_mul _) (fun i ↦ (hX i).const_mul _)]
  simp only [covariance_const_mul_left, covariance_const_mul_right, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem HasGaussianLaw.indepFun_of_covariance_euclidean
    {μ : Measure Ω} {X : Ω → EuclideanSpace ℝ ι} {Y : Ω → EuclideanSpace ℝ κ}
    (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) μ)
    (hcov : ∀ i j, cov[fun ω ↦ X ω i, fun ω ↦ Y ω j; μ] = 0) : IndepFun X Y μ := by
  have := hXY.isProbabilityMeasure
  apply hXY.indepFun_of_covariance_inner
  intro x y
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [covariance_fun_sum_fun_sum]
  · simp only [covariance_mul_const_left, covariance_mul_const_right, hcov,
      zero_mul, Finset.sum_const_zero]
  · intro i
    exact ((hXY.fst.map (EuclideanSpace.proj i)).memLp_two).mul_const _
  · intro j
    exact ((hXY.snd.map (EuclideanSpace.proj j)).memLp_two).mul_const _

theorem IndepFun.map_add_eq_compProd_gaussianChannel [DecidableEq ι] [DecidableEq κ]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → EuclideanSpace ℝ ι} {R : Ω → EuclideanSpace ℝ κ}
    (hYR : IndepFun Y R μ) (hY : Measurable Y) (hR : Measurable R)
    (B : Matrix κ ι ℝ) (V : Matrix κ κ ℝ)
    (hlaw : μ.map R = multivariateGaussian 0 V) :
    μ.map (fun ω ↦ (Y ω, B.toEuclideanLin (Y ω) + R ω)) =
      μ.map Y ⊗ₘ gaussianChannel B V := by
  rw [gaussianChannel_compProd_eq_map, ← hlaw,
    ← hYR.map_prod_eq_prod_map_map hY.aemeasurable hR.aemeasurable,
    Measure.map_map (by fun_prop) (hY.prodMk hR)]
  rfl

theorem multivariateGaussian_map_prod_add [DecidableEq ι] [DecidableEq κ] [DecidableEq ο]
    (A : Matrix ο ι ℝ) (D : Matrix ο κ ℝ)
    (m : EuclideanSpace ℝ ι) (n : EuclideanSpace ℝ κ)
    (Q : Matrix ι ι ℝ) (N : Matrix κ κ ℝ) (hQ : Q.PosSemidef) (hN : N.PosSemidef) :
    ((multivariateGaussian m Q).prod (multivariateGaussian n N)).map
      (fun p ↦ A.toEuclideanLin p.1 + D.toEuclideanLin p.2) =
      multivariateGaussian (A.toEuclideanLin m + D.toEuclideanLin n)
        (A * Q * A.transpose + D * N * D.transpose) := by
  have hAQ : (A * Q * A.transpose).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hQ.mul_mul_conjTranspose_same A
  have hDN : (D * N * D.transpose).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hN.mul_mul_conjTranspose_same D
  rw [← multivariateGaussian_conv _ _ _ _ hAQ hDN,
    ← multivariateGaussian_map_matrix A m Q hQ, ← multivariateGaussian_map_matrix D n N hN,
    Measure.conv, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

omit [Fintype ο] [Fintype τ] in
theorem covariance_matrix_multivariateGaussian [DecidableEq ι]
    (m : EuclideanSpace ℝ ι) (Q : Matrix ι ι ℝ) (hQ : Q.PosSemidef)
    (A : Matrix ο ι ℝ) (D : Matrix τ ι ℝ) (a : ο) (b : τ) :
    cov[fun x ↦ (A.toEuclideanLin x) a, fun x ↦ (D.toEuclideanLin x) b;
      multivariateGaussian m Q] = (A * Q * D.transpose) a b := by
  change cov[fun x : EuclideanSpace ℝ ι ↦ (A *ᵥ x.ofLp) a,
    fun x : EuclideanSpace ℝ ι ↦ (D *ᵥ x.ofLp) b; multivariateGaussian m Q] = _
  rw [covariance_matrix_mulVec]
  · simp_rw [covariance_eval_multivariateGaussian hQ]
  · intro i
    exact (IsGaussian.hasGaussianLaw_id.map (EuclideanSpace.proj i)).memLp_two

section Prod

variable {Ω' : Type*} [MeasurableSpace Ω']
  {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure μ] in
theorem covariance_fst_fst_prod {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    cov[fun p ↦ X p.1, fun p ↦ Y p.1; μ.prod ν] = cov[X, Y; μ] := by
  have hmap : (μ.prod ν).map Prod.fst = μ := by simp
  rw [← covariance_map_fun (by simpa only [hmap] using hX.aestronglyMeasurable)
    (by simpa only [hmap] using hY.aestronglyMeasurable) measurable_fst.aemeasurable, hmap]

theorem covariance_snd_snd_prod {X Y : Ω' → ℝ} (hX : MemLp X 2 ν) (hY : MemLp Y 2 ν) :
    cov[fun p ↦ X p.2, fun p ↦ Y p.2; μ.prod ν] = cov[X, Y; ν] := by
  have hmap : (μ.prod ν).map Prod.snd = ν := by simp
  rw [← covariance_map_fun (by simpa only [hmap] using hX.aestronglyMeasurable)
    (by simpa only [hmap] using hY.aestronglyMeasurable) measurable_snd.aemeasurable, hmap]

theorem covariance_prod_add {X Y : Ω → ℝ} {Z W : Ω' → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 ν) (hW : MemLp W 2 ν) :
    cov[fun p ↦ X p.1 + Z p.2, fun p ↦ Y p.1 + W p.2; μ.prod ν] =
      cov[X, Y; μ] + cov[Z, W; ν] := by
  change cov[(fun p : Ω × Ω' ↦ X p.1) + (fun p ↦ Z p.2),
    (fun p : Ω × Ω' ↦ Y p.1) + (fun p ↦ W p.2); μ.prod ν] = _
  rw [covariance_add_left (hX.comp_fst ν) (hZ.comp_snd μ)
      ((hY.comp_fst ν).add (hW.comp_snd μ)),
    covariance_add_right (hX.comp_fst ν) (hY.comp_fst ν) (hW.comp_snd μ),
    covariance_add_right (hZ.comp_snd μ) (hY.comp_fst ν) (hW.comp_snd μ),
    covariance_fst_fst_prod hX hY, covariance_snd_snd_prod hZ hW,
    covariance_fst_snd_prod hX hW, covariance_comm (fun p : Ω × Ω' ↦ Z p.2),
    covariance_fst_snd_prod hY hZ, add_zero, zero_add]

end Prod

theorem memLp_matrix_multivariateGaussian [DecidableEq ι]
    (m : EuclideanSpace ℝ ι) (Q : Matrix ι ι ℝ) (A : Matrix ο ι ℝ) (a : ο) :
    MemLp (fun x ↦ (A.toEuclideanLin x) a) 2 (multivariateGaussian m Q) := by
  exact (IsGaussian.hasGaussianLaw_id.map
    ((EuclideanSpace.proj a).comp A.toEuclideanLin.toContinuousLinearMap)).memLp_two

theorem covariance_gaussian_prod_matrix [DecidableEq ι] [DecidableEq κ]
    (m : EuclideanSpace ℝ ι) (n : EuclideanSpace ℝ κ)
    (Q : Matrix ι ι ℝ) (N : Matrix κ κ ℝ) (hQ : Q.PosSemidef) (hN : N.PosSemidef)
    (A : Matrix ο ι ℝ) (D : Matrix ο κ ℝ) (C : Matrix τ ι ℝ) (F : Matrix τ κ ℝ)
    (a : ο) (b : τ) :
    cov[fun p ↦ (A.toEuclideanLin p.1 + D.toEuclideanLin p.2) a,
      fun p ↦ (C.toEuclideanLin p.1 + F.toEuclideanLin p.2) b;
      (multivariateGaussian m Q).prod (multivariateGaussian n N)] =
      (A * Q * C.transpose + D * N * F.transpose) a b := by
  change cov[fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ ↦
      (A.toEuclideanLin p.1) a + (D.toEuclideanLin p.2) a,
    fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ ↦
      (C.toEuclideanLin p.1) b + (F.toEuclideanLin p.2) b; _] = _
  rw [covariance_prod_add (memLp_matrix_multivariateGaussian m Q A a)
    (memLp_matrix_multivariateGaussian m Q C b) (memLp_matrix_multivariateGaussian n N D a)
    (memLp_matrix_multivariateGaussian n N F b),
    covariance_matrix_multivariateGaussian m Q hQ,
    covariance_matrix_multivariateGaussian n N hN]
  rfl

noncomputable def matrixPair [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ο ι ℝ) (D : Matrix ο κ ℝ) :
    EuclideanSpace ℝ ι × EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ ο :=
  (A.toEuclideanLin.toContinuousLinearMap).comp (.fst ℝ _ _) +
    (D.toEuclideanLin.toContinuousLinearMap).comp (.snd ℝ _ _)

@[simp]
theorem matrixPair_apply [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ο ι ℝ) (D : Matrix ο κ ℝ)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) :
    matrixPair A D p = A.toEuclideanLin p.1 + D.toEuclideanLin p.2 := rfl

end ProbabilityTheory
