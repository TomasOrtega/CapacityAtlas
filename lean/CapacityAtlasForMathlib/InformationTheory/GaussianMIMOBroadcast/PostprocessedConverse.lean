/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.BlockKernel
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.Alignment
import CapacityAtlasForMathlib.InformationTheory.GaussianProductConditioning

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx n : ℕ} {rx : Fin K → ℕ}

noncomputable def codePrefixEntropy (c : Code K tx rx n)
    (E : Matrix (Fin tx) (Fin tx) ℝ) (k : ℕ) : ℝ :=
  MeasureInformation.prefixGaussianEntropy
    (fun i ↦ uniformFinLaw (c.messages i) (c.messages_pos i))
    (fun m ↦ flattenGaussianBlock (c.encode m)) (blockDiagonal (fun _ : Fin n ↦ E)) k

theorem receiverError_eq_integral_blockGaussian
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) (i : Fin K) (hN : (N i).PosSemidef) :
    receiverError H N c i = ∫ m,
      (multivariateGaussian (receiverBlockMean H c i m) (blockDiagonal (fun _ : Fin n ↦ N i))).real
        {y | (c.decode i).apply (unflattenGaussianBlock y) ≠ m i} ∂messageLaw c := by
  have hs : MeasurableSet
      {p : MessageTuple c × EuclideanSpace ℝ (Fin (rx i) × Fin n) |
        (c.decode i).apply (unflattenGaussianBlock p.2) ≠ p.1 i} :=
    (measurableSet_eq_fun ((decoder_measurable (c.decode i)).comp
      (measurable_unflattenGaussianBlock.comp measurable_snd))
      ((measurable_pi_apply i).comp measurable_fst)).compl
  rw [← receiverBlockKernel_error H N c i hN,
    MeasureInformation.real_compProd_finite (messageLaw c) _ _ hs]
  rfl

theorem fano_receiver_of_block_postprocess
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) (i : Fin K) (hN : (N i).PosSemidef)
    (E : Matrix (Fin tx) (Fin tx) ℝ) (hE : E.PosDef)
    (η : Kernel (EuclideanSpace ℝ (Fin tx × Fin n))
      (EuclideanSpace ℝ (Fin (rx i) × Fin n))) [IsMarkovKernel η]
    (hrow : ∀ m : MessageTuple c,
      η ∘ₘ multivariateGaussian (flattenGaussianBlock (c.encode m))
        (blockDiagonal (fun _ : Fin n ↦ E)) =
      multivariateGaussian (receiverBlockMean H c i m) (blockDiagonal (fun _ : Fin n ↦ N i))) :
    Real.log (c.messages i) ≤ codePrefixEntropy c E (i.val + 1) - codePrefixEntropy c E i.val +
      Real.log 2 + receiverError H N c i * Real.log (c.messages i) := by
  letI : ∀ j, Nonempty (Fin (c.messages j)) := fun j ↦ ⟨⟨0, c.messages_pos j⟩⟩
  have h := MeasureInformation.fano_postprocess_prefixGaussian
    (fun j ↦ uniformFinLaw (c.messages j) (c.messages_pos j))
    (fun m ↦ flattenGaussianBlock (c.encode m)) _ (posDef_blockDiagonal _ (fun _ ↦ hE)) η i
    (fun y ↦ (c.decode i).apply (unflattenGaussianBlock y))
    ((decoder_measurable (c.decode i)).comp measurable_unflattenGaussianBlock)
    (fun a ↦ by simpa only [Fintype.card_fin] using uniformFinLaw_singleton _ _ a)
  simp_rw [hrow] at h
  rw [receiverError_eq_integral_blockGaussian H N c i hN]
  simpa only [Fintype.card_fin, codePrefixEntropy, messageLaw] using h

theorem blockDiagonal_toEuclideanLin_flatten {r : ℕ}
    (H : Matrix (Fin r) (Fin tx) ℝ) (x : Fin n → EuclideanSpace ℝ (Fin tx)) :
    (blockDiagonal (fun _ : Fin n ↦ H)).toEuclideanLin (flattenGaussianBlock x) =
      flattenGaussianBlock (fun s ↦ H.toEuclideanLin (x s)) := by
  ext ⟨a, s⟩
  change (blockDiagonal (fun _ : Fin n ↦ H) *ᵥ fun p ↦ x p.2 p.1) (a, s) = (H *ᵥ (x s).ofLp) a
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, blockDiagonal_apply]

theorem gaussianBlock_postprocess_covariance {r : ℕ}
    (H : Matrix (Fin r) (Fin tx) ℝ) (N : Matrix (Fin r) (Fin r) ℝ)
    (E : Matrix (Fin tx) (Fin tx) ℝ) (hE : E.PosSemidef)
    (hR : (N - H * E * H.transpose).PosSemidef) (x : Fin n → EuclideanSpace ℝ (Fin tx)) :
    gaussianChannel (blockDiagonal (fun _ : Fin n ↦ H))
      (blockDiagonal (fun _ : Fin n ↦ N - H * E * H.transpose)) ∘ₘ
      multivariateGaussian (flattenGaussianBlock x) (blockDiagonal (fun _ : Fin n ↦ E)) =
      multivariateGaussian (flattenGaussianBlock (fun s ↦ H.toEuclideanLin (x s)))
        (blockDiagonal (fun _ : Fin n ↦ N)) := by
  rw [gaussianChannel_comp_multivariateGaussian _ _ (posSemidef_blockDiagonal _ (fun _ ↦ hR))
    _ _ (posSemidef_blockDiagonal _ (fun _ ↦ hE)), blockDiagonal_toEuclideanLin_flatten]
  congr 1
  rw [blockDiagonal_transpose, ← blockDiagonal_mul, ← blockDiagonal_mul, ← blockDiagonal_add]
  congr 1
  ext s
  simp

theorem fano_receiver_enhanced_alignment
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) (i : Fin K) (hN : (N i).PosDef)
    {δ : ℝ} (hδ : 0 < δ) (E : Matrix (Fin tx) (Fin tx) ℝ) (hE : E.PosDef)
    (hle : E ≤ alignmentNoise (H i) (N i) δ) :
    Real.log (c.messages i) ≤ codePrefixEntropy c E (i.val + 1) - codePrefixEntropy c E i.val +
      Real.log 2 + error H N c * Real.log (c.messages i) := by
  have hr := residualNoise_posDef_of_le_alignmentNoise (H i) (N i) hN hδ E hle
  have h := fano_receiver_of_block_postprocess H N c i hN.posSemidef E hE
    (gaussianChannel (blockDiagonal (fun _ : Fin n ↦ H i))
      (blockDiagonal (fun _ : Fin n ↦ N i - H i * E * (H i).transpose)))
    (fun m ↦ gaussianBlock_postprocess_covariance (H i) (N i) E hE.posSemidef hr.posSemidef (c.encode m))
  have hlog : 0 ≤ Real.log (c.messages i) := Real.log_nonneg (by exact_mod_cast c.messages_pos i)
  have herr := mul_le_mul_of_nonneg_right (receiverError_le_error H N c i) hlog
  linarith

end CapacityAtlas.Gaussian.MIMOBroadcast
