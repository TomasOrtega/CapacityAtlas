/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.LayeredStatistics

open MeasureTheory ProbabilityTheory Matrix Filter CapacityAtlas.MeasureChannel CapacityAtlas.MeasureBinning
open scoped BigOperators ENNReal Topology Classical

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx : ℕ}

noncomputable def blockLayerStateLikelihood {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) (n : ℕ) (x : LayerBlocks K tx n) : ℝ≥0∞ :=
  blockLayerDensity H N Q π k n (x, blockLayerAuxiliary H N Q π k n x)

@[fun_prop]
theorem measurable_blockLayerStateLikelihood {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) (n : ℕ) :
    Measurable (blockLayerStateLikelihood H N Q π k n) :=
  (measurable_blockLayerDensity H N Q π k n).comp
    (measurable_id.prodMk (measurable_blockLayerAuxiliary H N Q π k n))

theorem blockLayerStateLikelihood_update_of_lt {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k j : Fin K) (hjk : j < k) (n : ℕ)
    (x : LayerBlocks K tx n) (u : Fin n → EuclideanSpace ℝ (Fin tx)) :
    blockLayerStateLikelihood H N Q π k n (Function.update x j u) =
      blockLayerStateLikelihood H N Q π k n x := by
  unfold blockLayerStateLikelihood blockLayerDensity
  rw [blockLayerAuxiliary_update_of_lt H N Q π k j hjk,
    blockSuffixInput_update_of_le k j hjk.le]

theorem blockLayerStateLikelihood_update {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) (n : ℕ)
    (x : LayerBlocks K tx n) (u : Fin n → EuclideanSpace ℝ (Fin tx)) :
    blockLayerStateLikelihood H N Q π k n (blockLayerUpdate H N Q π k n (x, u)) =
      blockLayerDensity H N Q π k n (x, u) := by
  unfold blockLayerStateLikelihood
  rw [blockLayerAuxiliary_update]
  unfold blockLayerDensity blockLayerUpdate
  rw [blockSuffixInput_update_of_le k k le_rfl]

theorem gaussianStage_jointBad_eq {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (hQ : ∀ i, (Q i).PosSemidef) (π : Equiv.Perm (Fin K)) (k : Fin K)
    (hk : (Q (π k)).PosDef) (n L : ℕ) (T : ℝ) (hT : 0 < T)
    (σ : Measure (LayerBlocks K tx n)) [SFinite σ] :
    let D := gaussianRejectionStage H N Q hQ π k hk n L T hT
    (σ ⊗ₘ D.target) D.goodᶜ = (D.referenceKernel ∘ₘ σ)
      {x | ENNReal.ofReal T < blockLayerStateLikelihood H N Q π k n x} := by
  dsimp only
  change (σ ⊗ₘ blockLayerAuxiliaryKernel H N Q π k n) _ =
    (updateKernel (blockLayerAuxiliaryKernel H N Q π k n)
      (measurable_blockLayerUpdate H N Q π k n) ∘ₘ σ) _
  rw [updateKernel_comp_apply σ _ _
    (measurableSet_lt measurable_const (measurable_blockLayerStateLikelihood H N Q π k n))]
  congr 1
  ext p
  change (¬blockLayerDensity H N Q π k n p ≤ ENNReal.ofReal T) ↔
    ENNReal.ofReal T < blockLayerStateLikelihood H N Q π k n (blockLayerUpdate H N Q π k n p)
  rw [← not_le, blockLayerStateLikelihood_update H N Q π k n p.1 p.2]

section Sequence

variable {rx : Fin K → ℕ}
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (hQ : ∀ i, (Q i).PosDef)
    (π : Equiv.Perm (Fin K)) (order : ℕ → Fin K) (e : Equiv.Perm (Fin K))
    (horder : ∀ i : Fin K, order i.val = e i)
    (hdesc : ∀ i j : Fin K, i < j → order j.val < order i.val)
    (n : ℕ) (L : ℕ → ℕ) (T : ℕ → ℝ) (hT : ∀ i, 0 < T i)
    (initial : LayerBlocks K tx n)

include e horder hdesc

theorem gaussianStages_jointBad_eq_terminal (i : Fin K) :
    let D := gaussianStages H N Q hQ π order n L T hT
    ((sequenceReferenceLaw (fun j ↦ (D j).referenceKernel) initial i.val) ⊗ₘ (D i.val).target)
      (D i.val).goodᶜ = (blockLayerLaw Q π n)
        {x | ENNReal.ofReal (T i.val) < blockLayerStateLikelihood
          (H (π (order i.val))) (N (π (order i.val))) Q π (order i.val) n x} := by
  let D := gaussianStages H N Q hQ π order n L T hT
  let E : Set (LayerBlocks K tx n) :=
    {x | ENNReal.ofReal (T i.val) < blockLayerStateLikelihood
      (H (π (order i.val))) (N (π (order i.val))) Q π (order i.val) n x}
  have hE : MeasurableSet E := measurableSet_lt measurable_const
    (measurable_blockLayerStateLikelihood _ _ Q π _ n)
  have hbad : ((sequenceReferenceLaw (fun j ↦ (D j).referenceKernel) initial i.val) ⊗ₘ
      (D i.val).target) (D i.val).goodᶜ =
      sequenceReferenceLaw (fun j ↦ (D j).referenceKernel) initial (i.val + 1) E :=
    gaussianStage_jointBad_eq _ _ Q (fun j ↦ (hQ j).posSemidef) π _ (hQ _) n
      (L i.val) (T i.val) (hT i.val) _
  refine hbad.trans ?_
  have heq := sequenceReferenceLaw_apply_eq_of_invariant
    (fun j ↦ (D j).referenceKernel) initial hE (Nat.succ_le_of_lt i.isLt) ?_
  · rw [← heq, gaussianStages_referenceLaw H N Q hQ π order e horder]
  intro j hij hjK x
  change (gaussianRejectionStage _ _ Q (fun j ↦ (hQ j).posSemidef) π _ (hQ _) n
    (L j) (T j) (hT j)).referenceKernel x E = _
  rw [gaussianRejectionStage_referenceKernel]
  apply sampledKernel_univ_apply_invariant _ _ hE
  intro s u
  change (ENNReal.ofReal (T i.val) < blockLayerStateLikelihood _ _ Q π _ n
    (Function.update s (order j) u)) ↔ _
  rw [blockLayerStateLikelihood_update_of_lt _ _ Q π (order i.val) (order j)
    (hdesc i ⟨j, hjK⟩ (by exact Nat.lt_of_succ_le hij))]
  rfl

theorem gaussianStages_failure_le_terminal :
    let D := gaussianStages H N Q hQ π order n L T hT
    sequenceSampleLaw (fun j ↦ (D j).sampleLaw) K
      (sequenceSuccess initial (fun j ↦ (D j).next) (fun j ↦ (D j).success) K)ᶜ ≤
      ∑ i : Fin K, (2 : ℝ≥0∞) ^ i.val *
        (2 * (blockLayerLaw Q π n)
          {x | ENNReal.ofReal (T i.val) < blockLayerStateLikelihood
            (H (π (order i.val))) (N (π (order i.val))) Q π (order i.val) n x} +
          ENNReal.ofReal (Real.exp (-(L i.val : ℝ) * ((1 / 2 : ℝ) / T i.val)))) := by
  dsimp only
  have hb := rejectionSequence_failure_le (gaussianStages H N Q hQ π order n L T hT) initial K
  rw [← Fin.sum_univ_eq_sum_range] at hb
  apply hb.trans_eq
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  unfold RejectionStage.failureBound
  rw [gaussianStages_jointBad_eq_terminal H N Q hQ π order e horder hdesc n L T hT initial i]
  simp only [gaussianStages, gaussianRejectionStage, neg_mul]

omit e horder in
theorem gaussianStages_success_readback
    (samples : SequenceSamples
      (fun j ↦ (gaussianStages H N Q hQ π order n L T hT j).Samples) K)
    (hs : samples ∈ sequenceSuccess initial
      (fun j ↦ (gaussianStages H N Q hQ π order n L T hT j).next)
      (fun j ↦ (gaussianStages H N Q hQ π order n L T hT j).success) K) (i : Fin K) :
    ∃ l : Fin (L i.val), (sequenceSampleAt K samples i l).1 =
      blockLayerAuxiliary (H (π (order i.val))) (N (π (order i.val))) Q π (order i.val) n
        (sequenceState initial (fun j ↦ (gaussianStages H N Q hQ π order n L T hT j).next)
          K samples) := by
  let D := gaussianStages H N Q hQ π order n L T hT
  let P (j : ℕ) (x : LayerBlocks K tx n) (row : (D j).Samples) : Prop :=
    ∃ l : Fin (L j), (row l).1 =
      blockLayerAuxiliary (H (π (order j))) (N (π (order j))) Q π (order j) n x
  apply sequenceSuccess_readback initial (fun j ↦ (D j).next) (fun j ↦ (D j).success)
    P K ?_ ?_ samples hs i
  · intro j _ s row hrow
    obtain ⟨l, hl⟩ := exists_firstHit_eq hrow.2
    refine ⟨l, ?_⟩
    change (row l).1 = blockLayerAuxiliary _ _ Q π _ n (blockLayerUpdate _ _ Q π _ n _)
    rw [blockLayerAuxiliary_update]
    exact (congrArg Prod.fst hl).symm
  · intro j k hjk hkK s row fresh hrow
    obtain ⟨l, hl⟩ := hrow
    refine ⟨l, ?_⟩
    change (row l).1 = blockLayerAuxiliary _ _ Q π _ n (Function.update s (order k) _)
    rw [blockLayerAuxiliary_update_of_lt _ _ Q π (order j) (order k)
      (hdesc ⟨j, lt_trans hjk hkK⟩ ⟨k, hkK⟩ hjk)]
    exact hl

end Sequence

end CapacityAtlas.Gaussian.MIMOBroadcast
