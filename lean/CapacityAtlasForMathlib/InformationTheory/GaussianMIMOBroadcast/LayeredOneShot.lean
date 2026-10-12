/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.LayeredCode
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.LayeredBounds

open MeasureTheory ProbabilityTheory Matrix CapacityAtlas.MeasureBinning
open scoped BigOperators ENNReal Classical

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx : ℕ} {rx : Fin K → ℕ}

theorem blockLayerChannel_miss_eq
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (π : Equiv.Perm (Fin K))
    (k : Fin K) (n : ℕ) (F : ℝ≥0∞) :
    ((blockLayerLaw Q π n) ⊗ₘ blockLayerChannel (H (π k)) (N (π k)) n)
      {p | (blockLayerAuxiliary (H (π k)) (N (π k)) Q π k n p.1, p.2) ∉
        layerDecodingSet (H (π k)) (N (π k)) Q π k n F} = layeredMissTail H N Q π k n F := by
  have hE : MeasurableSet {p : LayerBlocks K tx n × (Fin n → EuclideanSpace ℝ (Fin (rx (π k)))) |
      (blockLayerAuxiliary (H (π k)) (N (π k)) Q π k n p.1, p.2) ∉
        layerDecodingSet (H (π k)) (N (π k)) Q π k n F} :=
    ((measurableSet_layerDecodingSet _ _ Q π k n F).preimage
      (((measurable_blockLayerAuxiliary _ _ Q π k n).comp measurable_fst).prodMk measurable_snd)).compl
  rw [blockLayerChannel_joint_apply _ _ n _ hE]
  simp only [layeredMissTail, layerDecodingSet, Set.mem_setOf_eq, not_lt]

theorem exists_layeredCode_error_le
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (hQ : ∀ i, (Q i).PosDef)
    (hN : ∀ i, (N i).PosDef) (π : Equiv.Perm (Fin K))
    (order : ℕ → Fin K) (e : Equiv.Perm (Fin K))
    (horder : ∀ i : Fin K, order i.val = e i)
    (hdesc : ∀ i j : Fin K, i < j → order j.val < order i.val)
    (n : ℕ) (L : ℕ → ℕ) (hL : ∀ j, 0 < L j) (T : ℕ → ℝ) (hT : ∀ j, 0 < T j)
    (M : Fin K → ℕ) (hM : ∀ i, 0 < M i) (P : ℝ) (hP : 0 ≤ P)
    (F : Fin K → ℝ≥0∞) (hF₀ : ∀ i, F i ≠ 0) (hFtop : ∀ i, F i ≠ ⊤)
    (active : Finset (Fin K)) (hinactive : ∀ i ∉ active, M (π (order i.val)) = 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : layeredErrorBound H N Q π order n L T M P F active ≤ ENNReal.ofReal ε) :
    ∃ c : Code K tx rx n, c.messages = M ∧ PowerAdmissible P c ∧ error H N c ≤ ε := by
  letI (r : Fin K) : Nonempty (Fin (M r)) := Fin.pos_iff_nonempty.mp (hM r)
  let D := gaussianStages H N Q hQ π order n L T hT
  let W (i : Fin K) := blockLayerChannel (H (π (order i.val))) (N (π (order i.val))) n (K := K)
  let aux (i : Fin K) := blockLayerAuxiliary (H (π (order i.val))) (N (π (order i.val))) Q π (order i.val) n
  let A (i : Fin K) := layerDecodingSet (H (π (order i.val))) (N (π (order i.val))) Q π (order i.val) n (F i)
  have haux (i : Fin K) : Measurable (aux i) := measurable_blockLayerAuxiliary _ _ Q π _ n
  have hA (i : Fin K) : MeasurableSet (A i) := measurableSet_layerDecodingSet _ _ Q π _ n (F i)
  have huniform (i : Fin K) (y : Fin n → EuclideanSpace ℝ (Fin (rx (π (order i.val))))) :
      (D i.val).candidate {u | (u, y) ∈ A i} ≤ (F i)⁻¹ :=
    layerDecodingSet_mass_le _ _ Q (fun j ↦ (hQ j).posSemidef) (hN _) π _ (hQ _) n
      (hF₀ i) (hFtop i) y
  obtain ⟨books, hbooks⟩ := exists_sequenceBooks_jointBound_le
    (M := fun j ↦ Fin (M (π (order j)))) (J := (r : Fin K) → Fin (M r))
    D (0 : LayerBlocks K tx n) 0 (measurableSet_layerPowerSet P n) K active W aux haux A hA
    (fun m j ↦ m (π (order j))) (fun i ↦ (F i)⁻¹) huniform
  refine ⟨layeredCode H N Q hQ π order e horder n L T hT M hM P F hL books, rfl,
    layeredCode_powerAdmissible H N Q hQ π order e horder n L T hT M hM hP F hL books, ?_⟩
  apply layeredCode_error_le_of_bookBound H N Q hQ π order e horder n L T hT M hM
    hdesc P F hL books active hinactive hε
  apply hbooks.trans (le_trans ?_ hbound)
  unfold layeredErrorBound
  apply Finset.sum_le_sum
  intro i _
  have hfailure : sequenceSampleLaw (fun j ↦ (D j).sampleLaw) K
      (sequenceSuccess 0 (fun j ↦ (D j).next) (fun j ↦ (D j).success) K)ᶜ ≤
        layeredFailureBound H N Q π order n L T := by
    simpa only [layeredFailureBound, layeredStateTail, blockLayerStateLikelihood, neg_mul] using
      gaussianStages_failure_le_terminal H N Q hQ π order e horder hdesc n L T hT 0
  have href : sequenceReferenceLaw (fun j ↦ (D j).referenceKernel) (0 : LayerBlocks K tx n) K =
      blockLayerLaw Q π n := gaussianStages_referenceLaw H N Q hQ π order e horder n L T hT 0
  rw [href]
  change _ + (2 : ℝ≥0∞) ^ K * layeredCostTail Q π n P +
      (2 : ℝ≥0∞) ^ K * ((blockLayerLaw Q π n) ⊗ₘ W i)
        {p | (aux i p.1, p.2) ∉ A i} +
      (Fintype.card (Fin (M (π (order i.val)))) - 1 : ℕ) * L i.val * (F i)⁻¹ ≤ _
  rw [show ((blockLayerLaw Q π n) ⊗ₘ W i) {p | (aux i p.1, p.2) ∉ A i} =
    layeredMissTail H N Q π (order i.val) n (F i) from blockLayerChannel_miss_eq H N Q π _ n (F i)]
  simp only [Fintype.card_fin]
  exact add_le_add (add_le_add (add_le_add hfailure le_rfl) le_rfl) le_rfl

end CapacityAtlas.Gaussian.MIMOBroadcast
