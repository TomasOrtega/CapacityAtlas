/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.GaussianLayers
import CapacityAtlasForMathlib.InformationTheory.GaussianDirtyPaper.BlockInformationDensity
import CapacityAtlasForMathlib.InformationTheory.MeasureRandomBinning.SequenceProducts

open MeasureTheory ProbabilityTheory Matrix CapacityAtlas.MeasureChannel CapacityAtlas.MeasureBinning
open scoped BigOperators ENNReal Classical

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx : ℕ}

abbrev LayerBlocks (K tx n : ℕ) := Fin K → Fin n → EuclideanSpace ℝ (Fin tx)

noncomputable def blockSuffixInput (k : Fin K) (n : ℕ) (x : LayerBlocks K tx n) :
    Fin n → EuclideanSpace ℝ (Fin tx) := fun t ↦ suffixInput k (fun j ↦ x j t)

@[fun_prop]
theorem measurable_blockSuffixInput (k : Fin K) (n : ℕ) :
    Measurable (blockSuffixInput (tx := tx) k n) := by
  unfold blockSuffixInput suffixInput
  fun_prop

theorem suffixInput_update_of_le (k j : Fin K) (hjk : j ≤ k)
    (x : Fin K → EuclideanSpace ℝ (Fin tx)) (v : EuclideanSpace ℝ (Fin tx)) :
    suffixInput k (Function.update x j v) = suffixInput k x := by
  apply Finset.sum_congr rfl
  intro i hi
  have hki : k < i := (Finset.mem_filter.mp hi).2
  exact Function.update_of_ne (ne_of_gt (lt_of_le_of_lt hjk hki)) _ _

theorem blockSuffixInput_update_of_le (k j : Fin K) (hjk : j ≤ k) (n : ℕ)
    (x : LayerBlocks K tx n) (v : Fin n → EuclideanSpace ℝ (Fin tx)) :
    blockSuffixInput k n (Function.update x j v) = blockSuffixInput k n x := by
  funext t
  change suffixInput k (fun i ↦ Function.update x j v i t) = _
  have heq : (fun i ↦ Function.update x j v i t) =
      Function.update (fun i ↦ x i t) j (v t) := by
    funext i
    by_cases hi : i = j <;> simp [hi]
  rw [heq, suffixInput_update_of_le k j hjk]
  rfl

noncomputable def blockLayerAuxiliary {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) (n : ℕ) (x : LayerBlocks K tx n) :
    Fin n → EuclideanSpace ℝ (Fin tx) := fun t ↦ layerAuxiliary H N Q π k (fun j ↦ x j t)

@[fun_prop]
theorem measurable_blockLayerAuxiliary {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) (n : ℕ) :
    Measurable (blockLayerAuxiliary H N Q π k n) := by
  unfold blockLayerAuxiliary
  fun_prop

theorem blockLayerAuxiliary_update_of_lt {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k j : Fin K) (hjk : j < k) (n : ℕ)
    (x : LayerBlocks K tx n) (v : Fin n → EuclideanSpace ℝ (Fin tx)) :
    blockLayerAuxiliary H N Q π k n (Function.update x j v) =
      blockLayerAuxiliary H N Q π k n x := by
  have hs := congrFun (blockSuffixInput_update_of_le k j hjk.le n x v)
  funext t
  change Function.update x j v k t + _ = x k t + _
  rw [Function.update_of_ne hjk.ne']
  exact congrArg (fun s ↦ x k t +
    (DirtyPaper.costaCoefficient H (Q (π k)) (layerNoiseCovariance H N Q π k) * H).toEuclideanLin s)
      (hs t)

noncomputable def blockLayerAuxiliaryKernel {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) (n : ℕ) :
    Kernel (LayerBlocks K tx n) (Fin n → EuclideanSpace ℝ (Fin tx)) :=
  (DirtyPaper.blockStateKernel H (Q (π k)) (layerNoiseCovariance H N Q π k) n).comap
    (blockSuffixInput k n) (measurable_blockSuffixInput k n)

instance {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) (n : ℕ) :
    IsMarkovKernel (blockLayerAuxiliaryKernel H N Q π k n) := by
  unfold blockLayerAuxiliaryKernel
  infer_instance

noncomputable def blockLayerDensity {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) (n : ℕ)
    (p : LayerBlocks K tx n × (Fin n → EuclideanSpace ℝ (Fin tx))) : ℝ≥0∞ :=
  DirtyPaper.blockStateLikelihood H (Q (π k)) (suffixCovariance Q π k)
    (layerNoiseCovariance H N Q π k) n (blockSuffixInput k n p.1, p.2)

@[fun_prop]
theorem measurable_blockLayerDensity {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) (n : ℕ) :
    Measurable (blockLayerDensity H N Q π k n) :=
  (DirtyPaper.measurable_blockStateLikelihood H (Q (π k)) (suffixCovariance Q π k)
    (layerNoiseCovariance H N Q π k) n).comp
      (((measurable_blockSuffixInput k n).comp measurable_fst).prodMk measurable_snd)

theorem blockLayerAuxiliaryKernel_eq_withDensity {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (hQ : ∀ i, (Q i).PosSemidef) (π : Equiv.Perm (Fin K)) (k : Fin K)
    (hk : (Q (π k)).PosDef) (n : ℕ) (x : LayerBlocks K tx n) :
    blockLayerAuxiliaryKernel H N Q π k n x =
      (DirtyPaper.blockAuxiliaryLaw H (Q (π k)) (suffixCovariance Q π k)
        (layerNoiseCovariance H N Q π k) n).withDensity
          (fun u ↦ blockLayerDensity H N Q π k n (x, u)) :=
  DirtyPaper.blockStateKernel_withDensity H (Q (π k)) (suffixCovariance Q π k)
    (layerNoiseCovariance H N Q π k) hk (suffixCovariance_posSemidef Q hQ π k) n _

noncomputable def blockLayerEncoderInput {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) (n : ℕ)
    (p : LayerBlocks K tx n × (Fin n → EuclideanSpace ℝ (Fin tx))) :
    Fin n → EuclideanSpace ℝ (Fin tx) :=
  DirtyPaper.blockEncoderInput H (Q (π k)) (layerNoiseCovariance H N Q π k) n
    (blockSuffixInput k n p.1, p.2)

@[fun_prop]
theorem measurable_blockLayerEncoderInput {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) (n : ℕ) :
    Measurable (blockLayerEncoderInput H N Q π k n) :=
  (DirtyPaper.measurable_blockEncoderInput H (Q (π k)) (layerNoiseCovariance H N Q π k) n).comp
    (((measurable_blockSuffixInput k n).comp measurable_fst).prodMk measurable_snd)

noncomputable def blockLayerUpdate {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) (n : ℕ)
    (p : LayerBlocks K tx n × (Fin n → EuclideanSpace ℝ (Fin tx))) : LayerBlocks K tx n :=
  Function.update p.1 k (blockLayerEncoderInput H N Q π k n p)

@[fun_prop]
theorem measurable_blockLayerUpdate {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) (n : ℕ) :
    Measurable (blockLayerUpdate H N Q π k n) := by
  unfold blockLayerUpdate
  exact measurable_update'.comp
    (measurable_fst.prodMk (measurable_blockLayerEncoderInput H N Q π k n))

theorem blockLayerAuxiliary_update {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) (n : ℕ)
    (x : LayerBlocks K tx n) (u : Fin n → EuclideanSpace ℝ (Fin tx)) :
    blockLayerAuxiliary H N Q π k n (blockLayerUpdate H N Q π k n (x, u)) = u := by
  have hs := congrFun (blockSuffixInput_update_of_le k k le_rfl n x
    (blockLayerEncoderInput H N Q π k n (x, u)))
  funext t
  change Function.update x k (blockLayerEncoderInput H N Q π k n (x, u)) k t + _ = u t
  rw [Function.update_self]
  change (u t - _) + _ = u t
  rw [show suffixInput k (fun j ↦ blockLayerUpdate H N Q π k n (x, u) j t) =
    blockSuffixInput k n x t from hs t]
  exact sub_add_cancel _ _

theorem blockLayerAuxiliaryKernel_map_encoderInput {r : ℕ}
    (H : Matrix (Fin r) (Fin tx) ℝ) (N : Matrix (Fin r) (Fin r) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (π : Equiv.Perm (Fin K))
    (k : Fin K) (n : ℕ) (x : LayerBlocks K tx n) :
    (blockLayerAuxiliaryKernel H N Q π k n x).map
      (fun u ↦ blockLayerEncoderInput H N Q π k n (x, u)) =
        DirtyPaper.blockStateLaw (Q (π k)) n := by
  change (Measure.pi (fun t : Fin n ↦ layerAuxiliaryKernel H N Q π k (fun j ↦ x j t))).map
    (fun u t ↦ DirtyPaper.encoderInput H (Q (π k)) (layerNoiseCovariance H N Q π k)
      (suffixInput k (fun j ↦ x j t)) (u t)) = _
  have hm (t : Fin n) : Measurable (fun u ↦
      DirtyPaper.encoderInput H (Q (π k)) (layerNoiseCovariance H N Q π k)
        (suffixInput k (fun j ↦ x j t)) u) :=
    (DirtyPaper.measurable_encoderInput H (Q (π k)) (layerNoiseCovariance H N Q π k)).comp
      (measurable_const.prodMk measurable_id)
  rw [Measure.pi_map_pi (fun t ↦ (hm t).aemeasurable)]
  congr 1
  funext t
  exact layerAuxiliaryKernel_map_encoderInput H N Q π k (fun j ↦ x j t)

theorem blockLayerUpdate_target_row {r : ℕ}
    (H : Matrix (Fin r) (Fin tx) ℝ) (N : Matrix (Fin r) (Fin r) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (π : Equiv.Perm (Fin K))
    (k : Fin K) (n : ℕ) (x : LayerBlocks K tx n) :
    updateKernel (blockLayerAuxiliaryKernel H N Q π k n) (measurable_blockLayerUpdate H N Q π k n) x =
      (DirtyPaper.blockStateLaw (Q (π k)) n).map (fun u ↦ Function.update x k u) := by
  have hm : Measurable (fun u ↦ blockLayerEncoderInput H N Q π k n (x, u)) :=
    (measurable_blockLayerEncoderInput H N Q π k n).comp measurable_prodMk_left
  rw [← blockLayerAuxiliaryKernel_map_encoderInput H N Q π k n x,
    Measure.map_map (measurable_update x) hm]
  rfl

noncomputable def gaussianRejectionStage {r : ℕ}
    (H : Matrix (Fin r) (Fin tx) ℝ) (N : Matrix (Fin r) (Fin r) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (hQ : ∀ i, (Q i).PosSemidef)
    (π : Equiv.Perm (Fin K)) (k : Fin K) (hk : (Q (π k)).PosDef)
    (n L : ℕ) (T : ℝ) (hT : 0 < T) :
    RejectionStage (LayerBlocks K tx n) (Fin n → EuclideanSpace ℝ (Fin tx)) where
  target := blockLayerAuxiliaryKernel H N Q π k n
  target_markov := inferInstance
  candidate := DirtyPaper.blockAuxiliaryLaw H (Q (π k)) (suffixCovariance Q π k)
    (layerNoiseCovariance H N Q π k) n
  candidate_probability := inferInstance
  density := blockLayerDensity H N Q π k n
  measurable_density := measurable_blockLayerDensity H N Q π k n
  target_eq_density := blockLayerAuxiliaryKernel_eq_withDensity H N Q hQ π k hk n
  good := {p | blockLayerDensity H N Q π k n p ≤ ENNReal.ofReal T}
  measurable_good := measurableSet_le (measurable_blockLayerDensity H N Q π k n) measurable_const
  threshold := T
  threshold_pos := hT
  density_le := fun _ hp ↦ hp
  update := blockLayerUpdate H N Q π k n
  measurable_update := measurable_blockLayerUpdate H N Q π k n
  fallback := (0, 0)
  count := L

theorem gaussianRejectionStage_referenceKernel {r : ℕ}
    (H : Matrix (Fin r) (Fin tx) ℝ) (N : Matrix (Fin r) (Fin r) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (hQ : ∀ i, (Q i).PosSemidef)
    (π : Equiv.Perm (Fin K)) (k : Fin K) (hk : (Q (π k)).PosDef)
    (n L : ℕ) (T : ℝ) (hT : 0 < T) :
    (gaussianRejectionStage H N Q hQ π k hk n L T hT).referenceKernel =
      sampledKernel (DirtyPaper.blockStateLaw (Q (π k)) n) MeasurableSet.univ
        (measurable_update' (a := k)) := by
  ext x E hE
  change updateKernel (blockLayerAuxiliaryKernel H N Q π k n)
      (measurable_blockLayerUpdate H N Q π k n) x E = _
  rw [blockLayerUpdate_target_row, Measure.map_apply (measurable_update x) hE,
    sampledKernel_apply _ MeasurableSet.univ (measurable_update' (a := k)) x hE]
  simp only [Set.mem_univ, true_and]
  rfl

noncomputable def blockLayerLaw (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (n : ℕ) : Measure (LayerBlocks K tx n) :=
  Measure.pi (fun k ↦ DirtyPaper.blockStateLaw (Q (π k)) n)

instance (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (n : ℕ) : IsProbabilityMeasure (blockLayerLaw Q π n) := by
  unfold blockLayerLaw
  infer_instance

noncomputable def gaussianStages {rx : Fin K → ℕ}
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (hQ : ∀ i, (Q i).PosDef)
    (π : Equiv.Perm (Fin K)) (order : ℕ → Fin K) (n : ℕ) (L : ℕ → ℕ)
    (T : ℕ → ℝ) (hT : ∀ i, 0 < T i) :
    ℕ → RejectionStage (LayerBlocks K tx n) (Fin n → EuclideanSpace ℝ (Fin tx)) :=
  fun i ↦ gaussianRejectionStage (H (π (order i))) (N (π (order i))) Q
    (fun j ↦ (hQ j).posSemidef) π (order i) (hQ (π (order i))) n (L i) (T i) (hT i)

theorem gaussianStages_referenceLaw {rx : Fin K → ℕ}
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (hQ : ∀ i, (Q i).PosDef)
    (π : Equiv.Perm (Fin K)) (order : ℕ → Fin K) (e : Equiv.Perm (Fin K))
    (horder : ∀ i : Fin K, order i.val = e i) (n : ℕ) (L : ℕ → ℕ)
    (T : ℕ → ℝ) (hT : ∀ i, 0 < T i) (initial : LayerBlocks K tx n) :
    sequenceReferenceLaw (fun i ↦ (gaussianStages H N Q hQ π order n L T hT i).referenceKernel)
      initial K = blockLayerLaw Q π n := by
  have hker : (fun i ↦ (gaussianStages H N Q hQ π order n L T hT i).referenceKernel) =
      (fun i ↦ sampledKernel (DirtyPaper.blockStateLaw (Q (π (order i))) n) MeasurableSet.univ
        (measurable_update' (a := order i))) := by
    funext i
    exact gaussianRejectionStage_referenceKernel _ _ _ _ _ _ _ _ _ _ _
  rw [hker, sequenceReferenceLaw_sampled]
  exact sequenceState_update_map_pi initial order
    (fun i ↦ DirtyPaper.blockStateLaw (Q (π (order i))) n)
    (fun k ↦ DirtyPaper.blockStateLaw (Q (π k)) n) K e horder
    (fun i ↦ by rw [horder i])

theorem gaussianStages_successLaw_le {rx : Fin K → ℕ}
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (hQ : ∀ i, (Q i).PosDef)
    (π : Equiv.Perm (Fin K)) (order : ℕ → Fin K) (e : Equiv.Perm (Fin K))
    (horder : ∀ i : Fin K, order i.val = e i) (n : ℕ) (L : ℕ → ℕ)
    (T : ℕ → ℝ) (hT : ∀ i, 0 < T i) (initial : LayerBlocks K tx n) :
    let D := gaussianStages H N Q hQ π order n L T hT
    sequenceSuccessLaw (fun i ↦ (D i).sampleLaw) initial (fun i ↦ (D i).next)
      (fun i ↦ (D i).success) K ≤ (2 : ℝ≥0∞) ^ K • blockLayerLaw Q π n := by
  dsimp only
  rw [← gaussianStages_referenceLaw H N Q hQ π order e horder n L T hT initial]
  exact rejectionSequence_successLaw_le _ initial K

end CapacityAtlas.Gaussian.MIMOBroadcast
