/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianDirtyPaper.Covariance
import CapacityAtlasForMathlib.InformationTheory.FiniteConditionalInformation
import CapacityAtlasForMathlib.Probability.GaussianChannel

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped MatrixOrder

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {ι ο : Type*} [Fintype ι] [Fintype ο] [DecidableEq ι] [DecidableEq ο]

noncomputable def alignmentNoise (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ) (δ : ℝ) :
    Matrix ι ι ℝ := (δ • 1 + H.transpose * N⁻¹ * H)⁻¹

theorem alignmentNoise_posDef (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (hN : N.PosDef) {δ : ℝ} (hδ : 0 < δ) : (alignmentNoise H N δ).PosDef := by
  apply Matrix.PosDef.inv
  apply (Matrix.PosDef.one.smul hδ).add_posSemidef
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    hN.inv.posSemidef.conjTranspose_mul_mul_same H

theorem inv_smul_one (δ : ℝ) (hδ : δ ≠ 0) :
    (δ⁻¹ • (1 : Matrix ι ι ℝ))⁻¹ = δ • 1 := by
  apply Matrix.inv_eq_left_inv
  simp [hδ]

theorem alignmentNoise_eq_residualCovariance (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (hN : N.PosDef) {δ : ℝ} (hδ : 0 < δ) :
    alignmentNoise H N δ = DirtyPaper.residualCovariance H (δ⁻¹ • 1) N := by
  rw [DirtyPaper.residualCovariance_eq_inverse H _ N
    (Matrix.PosDef.one.smul (inv_pos.mpr hδ)) hN, inv_smul_one δ hδ.ne']
  rfl

omit [DecidableEq ι] in
theorem alignment_residual_noise_eq (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosSemidef) (hN : N.PosDef) :
    N - H * DirtyPaper.residualCovariance H Q N * H.transpose =
      N * (DirtyPaper.outputCovariance H Q N)⁻¹ * N := by
  let D := H * Q * H.transpose
  let C := DirtyPaper.outputCovariance H Q N
  have hC := DirtyPaper.outputCovariance_posDef H Q N hQ hN
  have hl : N * C⁻¹ + D * C⁻¹ = 1 := by
    simpa only [C, DirtyPaper.outputCovariance, add_mul, D] using
      C.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hC.det_pos.ne')
  have hr : C⁻¹ * N + C⁻¹ * D = 1 := by
    simpa only [C, DirtyPaper.outputCovariance, mul_add, D] using
      C.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hC.det_pos.ne')
  have h₁ := congrArg (fun A ↦ A * N) hl
  have h₂ := congrArg (fun A ↦ D * A) hr
  simp only [add_mul, one_mul] at h₁
  simp only [mul_add, mul_one, ← Matrix.mul_assoc] at h₂
  have he : N - D + D * C⁻¹ * D = N * C⁻¹ * N := by
    calc
      _ = (N * C⁻¹ * N + D * C⁻¹ * N) -
          (D * C⁻¹ * N + D * C⁻¹ * D) + D * C⁻¹ * D := by rw [h₁, h₂]
      _ = _ := by abel
  calc
    _ = N - D + D * C⁻¹ * D := by
      dsimp only [DirtyPaper.residualCovariance, DirtyPaper.costaCoefficient, D, C]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      abel
    _ = _ := he

omit [DecidableEq ι] in
theorem alignment_residual_noise_posDef (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosSemidef) (hN : N.PosDef) :
    (N - H * DirtyPaper.residualCovariance H Q N * H.transpose).PosDef := by
  rw [alignment_residual_noise_eq H Q N hQ hN]
  have h := hN.isUnit.posDef_star_left_conjugate_iff.mpr
    (DirtyPaper.outputCovariance_posDef H Q N hQ hN).inv
  simpa only [Matrix.star_eq_conjTranspose, hN.isHermitian.eq] using h

theorem gaussianChannel_eq_postprocess_aligned (H : Matrix ο ι ℝ)
    (N : Matrix ο ο ℝ) (hN : N.PosDef) (Q : Matrix ι ι ℝ) (hQ : Q.PosDef) :
    gaussianChannel H N =
      gaussianChannel H (N - H * DirtyPaper.residualCovariance H Q N * H.transpose) ∘ₖ
        gaussianChannel 1 (DirtyPaper.residualCovariance H Q N) := by
  ext x : 1
  rw [Kernel.comp_apply, gaussianChannel_apply, gaussianChannel_apply]
  rw [gaussianChannel_comp_multivariateGaussian _ _
    (alignment_residual_noise_posDef H Q N hQ.posSemidef hN).posSemidef _ _
    (DirtyPaper.residualCovariance_posDef H Q N hQ hN).posSemidef, sub_add_cancel]
  congr 1
  simp

theorem gaussianChannel_eq_postprocess_alignmentNoise (H : Matrix ο ι ℝ)
    (N : Matrix ο ο ℝ) (hN : N.PosDef) {δ : ℝ} (hδ : 0 < δ) :
    gaussianChannel H N =
      gaussianChannel H (N - H * alignmentNoise H N δ * H.transpose) ∘ₖ
        gaussianChannel 1 (alignmentNoise H N δ) := by
  rw [alignmentNoise_eq_residualCovariance H N hN hδ]
  exact gaussianChannel_eq_postprocess_aligned H N hN _
    (Matrix.PosDef.one.smul (inv_pos.mpr hδ))

theorem alignmentNoise_inv (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (hN : N.PosDef) {δ : ℝ} (hδ : 0 < δ) :
    (alignmentNoise H N δ)⁻¹ = δ • 1 + H.transpose * N⁻¹ * H := by
  have hp : (δ • 1 + H.transpose * N⁻¹ * H).PosDef := by
    apply (Matrix.PosDef.one.smul hδ).add_posSemidef
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      hN.inv.posSemidef.conjTranspose_mul_mul_same H
  exact Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hp.det_pos.ne')

theorem mutualInfo_gaussianChannel_le_alignmentNoise
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (κ : Kernel α (EuclideanSpace ℝ ι)) [IsMarkovKernel κ]
    (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ) (hN : N.PosDef)
    {δ : ℝ} (hδ : 0 < δ) :
    MeasureInformation.mutualInfo (μ ⊗ₘ (gaussianChannel H N ∘ₖ κ)) ≤
      MeasureInformation.mutualInfo (μ ⊗ₘ (gaussianChannel 1 (alignmentNoise H N δ) ∘ₖ κ)) := by
  rw [gaussianChannel_eq_postprocess_alignmentNoise H N hN hδ, Kernel.comp_assoc]
  exact MeasureInformation.mutualInfo_kernel_comp_le μ _ _

theorem residualNoise_posDef_of_le_alignmentNoise (H : Matrix ο ι ℝ)
    (N : Matrix ο ο ℝ) (hN : N.PosDef) {δ : ℝ} (hδ : 0 < δ)
    (E : Matrix ι ι ℝ) (hE : E ≤ alignmentNoise H N δ) :
    (N - H * E * H.transpose).PosDef := by
  have hA : (N - H * alignmentNoise H N δ * H.transpose).PosDef := by
    rw [alignmentNoise_eq_residualCovariance H N hN hδ]
    exact alignment_residual_noise_posDef H _ N
      (Matrix.PosDef.one.smul (inv_pos.mpr hδ)).posSemidef hN
  have hD : (H * (alignmentNoise H N δ - E) * H.transpose).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      (Matrix.le_iff.mp hE).mul_mul_conjTranspose_same H
  have he : N - H * E * H.transpose =
      (N - H * alignmentNoise H N δ * H.transpose) +
        H * (alignmentNoise H N δ - E) * H.transpose := by
    simp only [Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [he]
  exact hA.add_posSemidef hD

end CapacityAtlas.Gaussian.MIMOBroadcast
