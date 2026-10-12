/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.PostprocessedConverse
import CapacityAtlasForMathlib.InformationTheory.GaussianMixtureEntropyBounds

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx n : ℕ} {rx : Fin K → ℕ}

theorem entropyWith_gaussianBlock (E : Matrix (Fin tx) (Fin tx) ℝ) (hE : E.PosDef) :
    MeasureInformation.entropyWith (multivariateGaussian (0 : EuclideanSpace ℝ (Fin tx × Fin n))
      (blockDiagonal (fun _ : Fin n ↦ E))) volume =
    n * MeasureInformation.entropyWith (multivariateGaussian 0 E) volume := by
  rw [MeasureInformation.entropyWith_multivariateGaussian _ _
    (posDef_blockDiagonal _ (fun _ ↦ hE)),
    MeasureInformation.entropyWith_multivariateGaussian _ E hE,
    log_det_blockDiagonal_posDef _ (fun _ ↦ hE)]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem codePrefixEntropy_zero (c : Code K tx rx n)
    (E : Matrix (Fin tx) (Fin tx) ℝ) (hE : E.PosDef) :
    codePrefixEntropy c E 0 = n * MeasureInformation.entropyWith (multivariateGaussian 0 E) volume := by
  rw [codePrefixEntropy, MeasureInformation.prefixGaussianEntropy_zero _ _ _
    (posDef_blockDiagonal _ (fun _ ↦ hE)), entropyWith_gaussianBlock E hE]

theorem codePrefixEntropy_all (c : Code K tx rx n) (E : Matrix (Fin tx) (Fin tx) ℝ) :
    codePrefixEntropy c E K = MeasureInformation.entropyWith
      (MeasureInformation.gaussianCodebookKernel (fun m ↦ flattenGaussianBlock (c.encode m))
        (blockDiagonal (fun _ : Fin n ↦ E)) ∘ₘ messageLaw c) volume := by
  exact MeasureInformation.prefixGaussianEntropy_all _ _ _

theorem integral_codeEnergy_le (c : Code K tx rx n) {P : ℝ} (hc : PowerAdmissible P c) :
    (∫ m, ∑ s, ∑ a, (c.encode m s a) ^ 2 ∂messageLaw c) ≤ n * P := by
  simpa only [PowerAdmissible, integral_fintype Integrable.of_finite, messageLaw_real_singleton,
    smul_eq_mul, ← Finset.mul_sum] using hc

theorem weighted_block_quadratic (T : Matrix (Fin tx) (Fin tx) ℝ) (hT : T.PosDef)
    {γ lam : ℝ} (hstat : γ • T⁻¹ = lam • 1) (x : Fin n → EuclideanSpace ℝ (Fin tx)) :
    γ * (flattenGaussianBlock x ⬝ᵥ
      (blockDiagonal (fun _ : Fin n ↦ T))⁻¹ *ᵥ flattenGaussianBlock x) =
      lam * ∑ s, ∑ a, (x s a) ^ 2 := by
  rw [inv_blockDiagonal_posDef _ (fun _ ↦ hT), dotProduct_blockDiagonal_mulVec]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have h := congrArg (fun A ↦ (x s).ofLp ⬝ᵥ A *ᵥ (x s).ofLp) hstat
  rw [Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, dotProduct_smul] at h
  simpa [flattenGaussianBlock, Matrix.mulVec, dotProduct, Finset.mul_sum,
    pow_two, mul_assoc, mul_left_comm, mul_comm] using h

theorem codePrefixEntropy_last_le (c : Code K tx rx n)
    (E S : Matrix (Fin tx) (Fin tx) ℝ) (hE : E.PosDef) (hS : S.PosSemidef)
    {P γ lam : ℝ} (hc : PowerAdmissible P c) (hγ : 0 ≤ γ) (hlam : 0 ≤ lam)
    (hstat : γ • (S + E)⁻¹ = lam • 1) (hcomp : lam * (P - trace S) = 0) :
    γ * codePrefixEntropy c E K ≤
      γ * (n * MeasureInformation.entropyWith (multivariateGaussian 0 (S + E)) volume) := by
  have hT := PosDef.posSemidef_add hS hE
  have h := MeasureInformation.entropyWith_gaussianCodebook_le_reference (messageLaw c)
    (fun m ↦ flattenGaussianBlock (c.encode m))
    (blockDiagonal (fun _ : Fin n ↦ E)) (blockDiagonal (fun _ : Fin n ↦ S + E))
    (posDef_blockDiagonal _ (fun _ ↦ hE)) (posDef_blockDiagonal _ (fun _ ↦ hT))
  rw [← codePrefixEntropy_all, entropyWith_gaussianBlock _ hT,
    inv_blockDiagonal_posDef _ (fun _ ↦ hT), ← blockDiagonal_mul, trace_blockDiagonal] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Fintype.card_prod, Nat.cast_mul] at h
  have htrace := congrArg (fun A ↦ trace (A * E)) hstat
  simp only [Matrix.smul_mul, trace_smul, smul_eq_mul, Matrix.one_mul] at htrace
  have hdim := congrArg (fun A ↦ trace (A * (S + E))) hstat
  rw [Matrix.smul_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hT.det_pos.ne'),
    trace_smul, trace_one, Matrix.smul_mul, Matrix.one_mul, trace_smul, trace_add] at hdim
  simp only [smul_eq_mul, Fintype.card_fin] at hdim
  have hquad : γ * (∫ m, flattenGaussianBlock (c.encode m) ⬝ᵥ
      blockDiagonal (fun _ : Fin n ↦ (S + E)⁻¹) *ᵥ flattenGaussianBlock (c.encode m) ∂messageLaw c) =
      lam * ∫ m, ∑ s, ∑ a, (c.encode m s a) ^ 2 ∂messageLaw c := by
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with m
    simpa only [inv_blockDiagonal_posDef _ (fun _ ↦ hT)] using
      weighted_block_quadratic (S + E) hT hstat (c.encode m)
  have hp := mul_le_mul_of_nonneg_left (integral_codeEnergy_le c hc) hlam
  have hw := mul_le_mul_of_nonneg_left h hγ
  nlinarith

end CapacityAtlas.Gaussian.MIMOBroadcast
