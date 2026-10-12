/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.Information
import CapacityAtlasForMathlib.InformationTheory.GaussianFiniteConditioning
import CapacityAtlasForMathlib.Probability.GaussianBlocks

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx n : ℕ} {rx : Fin K → ℕ}

theorem blockNoise_map_receiver
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ) (i : Fin K) :
    (blockNoise N n).map (fun z ↦ z i) =
      Measure.pi (fun _ : Fin n ↦ multivariateGaussian 0 (N i)) :=
  (measurePreserving_eval (fun j ↦
    Measure.pi (fun _ : Fin n ↦ multivariateGaussian 0 (N j))) i).map_eq

theorem blockNoise_map_flatten_receiver
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ) (i : Fin K)
    (hN : (N i).PosSemidef) :
    (blockNoise N n).map (fun z ↦ flattenGaussianBlock (z i)) =
      multivariateGaussian 0 (blockDiagonal (fun _ : Fin n ↦ N i)) := by
  change (blockNoise N n).map (flattenGaussianBlock ∘ fun z ↦ z i) = _
  rw [← Measure.map_map measurable_flattenGaussianBlock (measurable_pi_apply i),
    blockNoise_map_receiver]
  exact map_flatten_pi_multivariateGaussian_zero _ (fun _ ↦ hN)

theorem flatten_output
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (x : Fin n → EuclideanSpace ℝ (Fin tx))
    (z : (i : Fin K) → Fin n → EuclideanSpace ℝ (Fin (rx i))) (i : Fin K) :
    flattenGaussianBlock (output H x z i) =
      flattenGaussianBlock (fun s ↦ (H i).toEuclideanLin (x s)) + flattenGaussianBlock (z i) := rfl

theorem blockNoise_map_flatten_output
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (x : Fin n → EuclideanSpace ℝ (Fin tx)) (i : Fin K) (hN : (N i).PosSemidef) :
    (blockNoise N n).map (fun z ↦ flattenGaussianBlock (output H x z i)) =
      multivariateGaussian (flattenGaussianBlock (fun s ↦ (H i).toEuclideanLin (x s)))
        (blockDiagonal (fun _ : Fin n ↦ N i)) := by
  simp_rw [flatten_output]
  change (blockNoise N n).map
    ((fun y ↦ flattenGaussianBlock (fun s ↦ (H i).toEuclideanLin (x s)) + y) ∘
      fun z ↦ flattenGaussianBlock (z i)) = _
  rw [← Measure.map_map (by fun_prop)
    (show Measurable (fun z : (j : Fin K) → Fin n → EuclideanSpace ℝ (Fin (rx j)) ↦
      flattenGaussianBlock (z i)) from
      measurable_flattenGaussianBlock.comp (measurable_pi_apply i)),
    blockNoise_map_flatten_receiver N i hN, multivariateGaussian_map_const_add, add_zero]

noncomputable def receiverBlockMean
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (c : Code K tx rx n) (i : Fin K) (m : MessageTuple c) :
    EuclideanSpace ℝ (Fin (rx i) × Fin n) :=
  flattenGaussianBlock (fun s ↦ (H i).toEuclideanLin (c.encode m s))

noncomputable def receiverBlockKernel
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) (i : Fin K) :
    Kernel (MessageTuple c) (EuclideanSpace ℝ (Fin (rx i) × Fin n)) :=
  MeasureInformation.gaussianCodebookKernel (receiverBlockMean H c i)
    (blockDiagonal (fun _ : Fin n ↦ N i))

instance receiverBlockKernel_isMarkovKernel
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) (i : Fin K) : IsMarkovKernel (receiverBlockKernel H N c i) := by
  unfold receiverBlockKernel
  infer_instance

theorem receiverBlockKernel_apply
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) (i : Fin K) (hN : (N i).PosSemidef) (m : MessageTuple c) :
    receiverBlockKernel H N c i m =
      (blockNoise N n).map (fun z ↦ flattenGaussianBlock (output H (c.encode m) z i)) :=
  (blockNoise_map_flatten_output H N (c.encode m) i hN).symm

theorem receiverBlockKernel_joint_eq_experiment
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) (i : Fin K) (hN : (N i).PosSemidef) :
    messageLaw c ⊗ₘ receiverBlockKernel H N c i =
      (experiment N c).map (fun p ↦ (p.1, flattenGaussianBlock (receivedRV H c i p))) := by
  have hm : Measurable (fun p : ExperimentSpace c ↦
      (p.1, flattenGaussianBlock (receivedRV H c i p))) :=
    measurable_fst.prodMk (measurable_flattenGaussianBlock.comp (measurable_receivedRV H c i))
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply hm hs,
    experiment, Measure.prod_apply (hm hs)]
  apply lintegral_congr
  intro m
  rw [receiverBlockKernel_apply H N c i hN m,
    Measure.map_apply (show Measurable (fun z ↦ flattenGaussianBlock (output H (c.encode m) z i)) from
      measurable_flattenGaussianBlock.comp (measurable_output H (c.encode m) i))
      (measurable_prodMk_left hs)]
  rfl

theorem receiverBlockKernel_error
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) (i : Fin K) (hN : (N i).PosSemidef) :
    (messageLaw c ⊗ₘ receiverBlockKernel H N c i).real
      {p | (c.decode i).apply (unflattenGaussianBlock p.2) ≠ p.1 i} = receiverError H N c i := by
  have hs : MeasurableSet
      {p : MessageTuple c × EuclideanSpace ℝ (Fin (rx i) × Fin n) |
        (c.decode i).apply (unflattenGaussianBlock p.2) ≠ p.1 i} :=
    (measurableSet_eq_fun ((decoder_measurable (c.decode i)).comp
      (measurable_unflattenGaussianBlock.comp measurable_snd))
      ((measurable_pi_apply i).comp measurable_fst)).compl
  rw [receiverBlockKernel_joint_eq_experiment H N c i hN, Measure.real,
    Measure.map_apply (show Measurable (fun p ↦ (p.1, flattenGaussianBlock (receivedRV H c i p))) from
      measurable_fst.prodMk
        (measurable_flattenGaussianBlock.comp (measurable_receivedRV H c i))) hs]
  exact experiment_receiver_error H N c i

end CapacityAtlas.Gaussian.MIMOBroadcast
