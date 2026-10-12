/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.LayeredReadback
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.Basic
import CapacityAtlasForMathlib.InformationTheory.MeasureRandomBinning.SequenceDecoder

open MeasureTheory ProbabilityTheory Matrix CapacityAtlas.MeasureChannel CapacityAtlas.MeasureBinning
open scoped BigOperators ENNReal Classical

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx : ℕ}

noncomputable def blockLayerChannel {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (n : ℕ) :
    Kernel (LayerBlocks K tx n) (Fin n → EuclideanSpace ℝ (Fin r)) :=
  (Kernel.id ×ₖ Kernel.const (LayerBlocks K tx n) (DirtyPaper.blockStateLaw N n)).map
    (blockLayerObservation H n)

instance {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ) (N : Matrix (Fin r) (Fin r) ℝ) (n : ℕ) :
    IsMarkovKernel (blockLayerChannel (K := K) H N n) := by
  unfold blockLayerChannel
  exact Kernel.IsMarkovKernel.map _ (measurable_blockLayerObservation H n)

theorem blockLayerChannel_apply {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (n : ℕ) (x : LayerBlocks K tx n) :
    blockLayerChannel H N n x = (DirtyPaper.blockStateLaw N n).map
      (fun z ↦ blockLayerObservation H n (x, z)) := by
  rw [blockLayerChannel, Kernel.map_apply _ (measurable_blockLayerObservation H n),
    Kernel.prod_apply]
  simp only [Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod]
  rw [Measure.map_map (measurable_blockLayerObservation H n) measurable_prodMk_left]
  rfl

theorem blockLayerChannel_joint_apply {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (n : ℕ) (σ : Measure (LayerBlocks K tx n)) [SFinite σ]
    {E : Set (LayerBlocks K tx n × (Fin n → EuclideanSpace ℝ (Fin r)))} (hE : MeasurableSet E) :
    (σ ⊗ₘ blockLayerChannel H N n) E =
      (σ.prod (DirtyPaper.blockStateLaw N n)) {p | (p.1, blockLayerObservation H n p) ∈ E} := by
  have hevent : MeasurableSet {p : LayerBlocks K tx n × (Fin n → EuclideanSpace ℝ (Fin r)) |
      (p.1, blockLayerObservation H n p) ∈ E} :=
    hE.preimage (measurable_fst.prodMk (measurable_blockLayerObservation H n))
  rw [Measure.compProd_apply hE, Measure.prod_apply hevent]
  apply lintegral_congr
  intro x
  rw [blockLayerChannel_apply, Measure.map_apply
    (show Measurable (fun z ↦ blockLayerObservation H n (x, z)) from
      (measurable_blockLayerObservation H n).comp measurable_prodMk_left)
    (hE.preimage measurable_prodMk_left)]
  rfl

theorem blockLayerChannel_eq_blockNoise {rx : Fin K → ℕ}
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ) (n : ℕ)
    (x : LayerBlocks K tx n) (r : Fin K)
    {E : Set (Fin n → EuclideanSpace ℝ (Fin (rx r)))} (hE : MeasurableSet E) :
    blockLayerChannel (H r) (N r) n x E =
      blockNoise N n {z | output H (blockTotalInput n x) z r ∈ E} := by
  rw [blockLayerChannel_apply, Measure.map_apply
    (show Measurable (fun z ↦ blockLayerObservation (H r) n (x, z)) from
      (measurable_blockLayerObservation (H r) n).comp measurable_prodMk_left) hE]
  have hm := measurePreserving_eval (fun j ↦ DirtyPaper.blockStateLaw (N j) n) r
  exact (hm.measure_preimage (hE.preimage
    ((measurable_blockLayerObservation (H r) n).comp measurable_prodMk_left)).nullMeasurableSet).symm

def layerPowerSet (P : ℝ) (n : ℕ) : Set (LayerBlocks K tx n) :=
  {x | DirtyPaper.blockEnergy n (blockTotalInput n x) ≤ (n : ℝ) * P}

theorem measurableSet_layerPowerSet (P : ℝ) (n : ℕ) :
    MeasurableSet (layerPowerSet (K := K) (tx := tx) P n) :=
  measurableSet_le ((DirtyPaper.measurable_blockEnergy n).comp (measurable_blockTotalInput n))
    measurable_const

theorem zero_mem_layerPowerSet {P : ℝ} (hP : 0 ≤ P) (n : ℕ) :
    (0 : LayerBlocks K tx n) ∈ layerPowerSet P n := by
  simp only [layerPowerSet, Set.mem_setOf_eq, DirtyPaper.blockEnergy, iidSum,
    blockTotalInput, Pi.zero_apply, Finset.sum_const_zero, norm_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  positivity

noncomputable def layerDecodingSet {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) (n : ℕ) (F : ℝ≥0∞) :
    Set ((Fin n → EuclideanSpace ℝ (Fin tx)) × (Fin n → EuclideanSpace ℝ (Fin r))) :=
  {p | F < DirtyPaper.blockObservationLikelihood H (Q (π k)) (suffixCovariance Q π k)
    (layerNoiseCovariance H N Q π k) n p}

theorem measurableSet_layerDecodingSet {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) (n : ℕ) (F : ℝ≥0∞) :
    MeasurableSet (layerDecodingSet H N Q π k n F) := measurableSet_lt measurable_const
      (DirtyPaper.measurable_blockObservationLikelihood H (Q (π k)) (suffixCovariance Q π k)
        (layerNoiseCovariance H N Q π k) n)

theorem layerDecodingSet_mass_le {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (hQ : ∀ i, (Q i).PosSemidef) (hN : N.PosDef) (π : Equiv.Perm (Fin K))
    (k : Fin K) (hk : (Q (π k)).PosDef) (n : ℕ) {F : ℝ≥0∞}
    (hF₀ : F ≠ 0) (hFtop : F ≠ ⊤) (y : Fin n → EuclideanSpace ℝ (Fin r)) :
    (DirtyPaper.blockAuxiliaryLaw H (Q (π k)) (suffixCovariance Q π k)
      (layerNoiseCovariance H N Q π k) n) {u | (u, y) ∈ layerDecodingSet H N Q π k n F} ≤ F⁻¹ :=
  reverseLikelihood_threshold_mass_le
    (DirtyPaper.blockReverseKernel H (Q (π k)) (layerNoiseCovariance H N Q π k) n) _ _
    (DirtyPaper.measurable_blockObservationLikelihood H (Q (π k)) (suffixCovariance Q π k)
      (layerNoiseCovariance H N Q π k) n)
    (DirtyPaper.blockReverseKernel_withDensity H (Q (π k)) (suffixCovariance Q π k)
      (layerNoiseCovariance H N Q π k) hk (suffixCovariance_posSemidef Q hQ π k)
        (layerNoiseCovariance_posDef H N Q hQ hN π k) n) hF₀ hFtop y

theorem error_eq_ennreal_average {rx : Fin K → ℕ}
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ) {n : ℕ}
    (c : Code K tx rx n) :
    error H N c = ((Fintype.card ((i : Fin K) → Fin (c.messages i)) : ℝ≥0∞)⁻¹ *
      ∑ m, blockNoise N n (errorEvent H c m)).toReal := by
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top _ _), card_messages]
  rfl

theorem error_le_of_ennreal_receiverBounds {rx : Fin K → ℕ}
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ) {n : ℕ}
    (c : Code K tx rx n) (e : Equiv.Perm (Fin K)) (active : Finset (Fin K))
    (hinactive : ∀ i ∉ active, c.messages (e i) = 1)
    (B : ((i : Fin K) → Fin (c.messages i)) → Fin K → ℝ≥0∞)
    (hB : ∀ m i, i ∈ active → blockNoise N n
      {z | (c.decode (e i)).apply (output H (c.encode m) z (e i)) ≠ m (e i)} ≤ B m i)
    {ε : ℝ} (hε : 0 ≤ ε)
    (havg : (Fintype.card ((i : Fin K) → Fin (c.messages i)) : ℝ≥0∞)⁻¹ *
      ∑ m, ∑ i ∈ active, B m i ≤ ENNReal.ofReal ε) : error H N c ≤ ε := by
  have hm (m : (i : Fin K) → Fin (c.messages i)) :
      blockNoise N n (errorEvent H c m) ≤ ∑ i ∈ active, B m i := by
    have hsub : errorEvent H c m ⊆ ⋃ i ∈ active,
        {z | (c.decode (e i)).apply (output H (c.encode m) z (e i)) ≠ m (e i)} := by
      intro z hz
      obtain ⟨r, hr⟩ := hz
      let i := e.symm r
      have her : e i = r := e.apply_symm_apply r
      have hi : i ∈ active := by
        by_contra hnot
        have hcount : c.messages r = 1 := by rw [← her]; exact hinactive i hnot
        have heq : (c.decode r).apply (output H (c.encode m) z r) = m r := by
          apply Fin.ext
          have h₁ := ((c.decode r).apply (output H (c.encode m) z r)).isLt
          have h₂ := (m r).isLt
          omega
        exact hr heq
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
        ⟨hi, (congrArg (fun r ↦ (c.decode r).apply (output H (c.encode m) z r) ≠ m r) her).mpr hr⟩⟩
    exact (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans
      (Finset.sum_le_sum (fun i hi ↦ hB m i hi)))
  have htotal : (Fintype.card ((i : Fin K) → Fin (c.messages i)) : ℝ≥0∞)⁻¹ *
      ∑ m, blockNoise N n (errorEvent H c m) ≤ ENNReal.ofReal ε :=
    (mul_le_mul_right (Finset.sum_le_sum (fun m _ ↦ hm m)) _).trans havg
  rw [error_eq_ennreal_average]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top htotal).trans_eq (ENNReal.toReal_ofReal hε)

section Code

variable {rx : Fin K → ℕ}
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (hQ : ∀ i, (Q i).PosDef)
    (π : Equiv.Perm (Fin K)) (order : ℕ → Fin K) (e : Equiv.Perm (Fin K))
    (horder : ∀ i : Fin K, order i.val = e i)
    (n : ℕ) (L : ℕ → ℕ) (T : ℕ → ℝ) (hT : ∀ i, 0 < T i)
    (M : Fin K → ℕ) (hM : ∀ i, 0 < M i)

abbrev LayeredBooks := SequenceSamples
  (fun j ↦ Fin (M (π (order j))) →
    (gaussianStages H N Q hQ π order n L T hT j).Samples) K

def stageReceiverEquiv : Equiv.Perm (Fin K) := e.trans π

theorem stageReceiverEquiv_apply (i : Fin K) :
    stageReceiverEquiv π e i = π (e i) := rfl

noncomputable def layeredStageDecoder (hM : ∀ i, 0 < M i)
    (F : Fin K → ℝ≥0∞) (hL : ∀ j, 0 < L j)
    (books : LayeredBooks H N Q hQ π order n L T hT M) (i : Fin K) :
    Decoder (Fin n → EuclideanSpace ℝ (Fin (rx (π (order i.val))))) (M (π (order i.val))) := by
  letI : Nonempty (Fin (M (π (order i.val)))) := Fin.pos_iff_nonempty.mp (hM _)
  letI : Nonempty (Fin (gaussianStages H N Q hQ π order n L T hT i.val).count) := by
    change Nonempty (Fin (L i.val))
    exact Fin.pos_iff_nonempty.mp (hL _)
  let A := layerDecodingSet (H (π (order i.val))) (N (π (order i.val))) Q π (order i.val) n (F i)
  let row := fun m l ↦ (sequenceSampleAt K books i m l).1
  exact ⟨binningDecoder A row,
    fun m ↦ (measurable_binningDecoder (measurableSet_layerDecodingSet _ _ Q π _ n (F i)) row)
      (measurableSet_singleton m)⟩

noncomputable def layeredCode (P : ℝ) (F : Fin K → ℝ≥0∞) (hL : ∀ j, 0 < L j)
    (books : LayeredBooks H N Q hQ π order n L T hT M) : Code K tx rx n where
  messages := M
  messages_pos := hM
  encode m := blockTotalInput n (safeSequenceState (gaussianStages H N Q hQ π order n L T hT)
    0 0 (layerPowerSet P n) K (selectedRows (fun j ↦ m (π (order j))) K books))
  decode r := by
    let i := (stageReceiverEquiv π e).symm r
    have hr : π (order i.val) = r := by
      rw [horder i]
      exact (stageReceiverEquiv π e).apply_symm_apply r
    exact hr ▸ layeredStageDecoder H N Q hQ π order n L T hT M hM F hL books i

theorem layeredCode_decode_stage (P : ℝ) (F : Fin K → ℝ≥0∞) (hL : ∀ j, 0 < L j)
    (books : LayeredBooks H N Q hQ π order n L T hT M) (i : Fin K) :
    (layeredCode H N Q hQ π order e horder n L T hT M hM P F hL books).decode (π (order i.val)) =
      layeredStageDecoder H N Q hQ π order n L T hT M hM F hL books i := by
  have hi : (stageReceiverEquiv π e).symm (π (order i.val)) = i := by
    rw [horder i]
    exact (stageReceiverEquiv π e).symm_apply_apply i
  dsimp only [layeredCode]
  apply eq_of_heq
  rw [eqRec_heq_iff]
  congr 1

include horder in
theorem layeredCode_stage_error_eq (P : ℝ) (F : Fin K → ℝ≥0∞) (hL : ∀ j, 0 < L j)
    (books : LayeredBooks H N Q hQ π order n L T hT M)
    (m : (r : Fin K) → Fin (M r)) (i : Fin K) :
    let c := layeredCode H N Q hQ π order e horder n L T hT M hM P F hL books
    blockNoise N n {z | (c.decode (π (order i.val))).apply
        (output H (c.encode m) z (π (order i.val))) ≠ m (π (order i.val))} =
      blockLayerChannel (H (π (order i.val))) (N (π (order i.val))) n
        (safeSequenceState (gaussianStages H N Q hQ π order n L T hT) 0 0 (layerPowerSet P n) K
          (selectedRows (fun j ↦ m (π (order j))) K books))
        {y | (layeredStageDecoder H N Q hQ π order n L T hT M hM F hL books i).apply y ≠
          m (π (order i.val))} := by
  dsimp only
  rw [layeredCode_decode_stage]
  exact (blockLayerChannel_eq_blockNoise H N n _ _
    (show MeasurableSet {y | (layeredStageDecoder H N Q hQ π order n L T hT M hM F hL books i).apply y ≠
      m (π (order i.val))} from
      ((layeredStageDecoder H N Q hQ π order n L T hT M hM F hL books i).measurable_fiber _).compl)).symm

theorem layeredCode_stage_error_le
    (hdesc : ∀ i j : Fin K, i < j → order j.val < order i.val)
    (P : ℝ) (F : Fin K → ℝ≥0∞) (hL : ∀ j, 0 < L j)
    (books : LayeredBooks H N Q hQ π order n L T hT M)
    (m : (r : Fin K) → Fin (M r)) (i : Fin K) :
    let c := layeredCode H N Q hQ π order e horder n L T hT M hM P F hL books
    blockNoise N n {z | (c.decode (π (order i.val))).apply
        (output H (c.encode m) z (π (order i.val))) ≠ m (π (order i.val))} ≤
      sequenceReceiverBound (gaussianStages H N Q hQ π order n L T hT) 0 0 (layerPowerSet P n)
        (blockLayerChannel (H (π (order i.val))) (N (π (order i.val))) n)
        (blockLayerAuxiliary (H (π (order i.val))) (N (π (order i.val))) Q π (order i.val) n)
        (layerDecodingSet (H (π (order i.val))) (N (π (order i.val))) Q π (order i.val) n (F i))
        (fun j ↦ m (π (order j))) K i books := by
  dsimp only
  rw [layeredCode_stage_error_eq]
  letI (j : ℕ) : Nonempty (Fin (M (π (order j)))) := Fin.pos_iff_nonempty.mp (hM _)
  letI : Nonempty (Fin (gaussianStages H N Q hQ π order n L T hT i.val).count) := by
    change Nonempty (Fin (L i.val))
    exact Fin.pos_iff_nonempty.mp (hL _)
  exact sequenceReceiver_error_le _ 0 0 _ _ _ _ (fun j ↦ m (π (order j))) K i
    (fun samples hs ↦ gaussianStages_success_readback H N Q hQ π order hdesc n L T hT 0 samples hs i) books

theorem layeredCode_error_le_of_bookBound
    (hdesc : ∀ i j : Fin K, i < j → order j.val < order i.val)
    (P : ℝ) (F : Fin K → ℝ≥0∞) (hL : ∀ j, 0 < L j)
    (books : LayeredBooks H N Q hQ π order n L T hT M) (active : Finset (Fin K))
    (hinactive : ∀ i ∉ active, M (π (order i.val)) = 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hbook : (Fintype.card ((r : Fin K) → Fin (M r)) : ℝ≥0∞)⁻¹ *
      ∑ m : (r : Fin K) → Fin (M r), ∑ i ∈ active,
        sequenceReceiverBound (gaussianStages H N Q hQ π order n L T hT) 0 0 (layerPowerSet P n)
          (blockLayerChannel (H (π (order i.val))) (N (π (order i.val))) n)
          (blockLayerAuxiliary (H (π (order i.val))) (N (π (order i.val))) Q π (order i.val) n)
          (layerDecodingSet (H (π (order i.val))) (N (π (order i.val))) Q π (order i.val) n (F i))
          (fun j ↦ m (π (order j))) K i books ≤ ENNReal.ofReal ε) :
    error H N (layeredCode H N Q hQ π order e horder n L T hT M hM P F hL books) ≤ ε := by
  let code := layeredCode H N Q hQ π order e horder n L T hT M hM P F hL books
  have hrecv (i : Fin K) : stageReceiverEquiv π e i = π (order i.val) := by rw [horder i]; rfl
  apply error_le_of_ennreal_receiverBounds H N code (stageReceiverEquiv π e) active
    (fun i hi ↦ (congrArg M (hrecv i)).trans (hinactive i hi))
    (fun m i ↦ sequenceReceiverBound (gaussianStages H N Q hQ π order n L T hT)
      0 0 (layerPowerSet P n) (blockLayerChannel (H (π (order i.val))) (N (π (order i.val))) n)
      (blockLayerAuxiliary (H (π (order i.val))) (N (π (order i.val))) Q π (order i.val) n)
      (layerDecodingSet (H (π (order i.val))) (N (π (order i.val))) Q π (order i.val) n (F i))
      (fun j ↦ m (π (order j))) K i books) ?_ hε hbook
  intro m i _
  have heq := congrArg (fun r ↦ blockNoise N n
    {z | (code.decode r).apply (output H (code.encode m) z r) ≠ m r}) (hrecv i)
  exact heq.trans_le (layeredCode_stage_error_le H N Q hQ π order e horder n L T hT M hM
    hdesc P F hL books m i)

theorem layeredCode_powerAdmissible {P : ℝ} (hP : 0 ≤ P) (F : Fin K → ℝ≥0∞)
    (hL : ∀ j, 0 < L j) (books : LayeredBooks H N Q hQ π order n L T hT M) :
    PowerAdmissible P (layeredCode H N Q hQ π order e horder n L T hT M hM P F hL books) := by
  let code := layeredCode H N Q hQ π order e horder n L T hT M hM P F hL books
  have hm (m : (i : Fin K) → Fin (code.messages i)) :
      (∑ s, ∑ a, (code.encode m s a) ^ 2) ≤ (n : ℝ) * P := by
    have hh := safeSequenceState_mem (gaussianStages H N Q hQ π order n L T hT)
      (0 : LayerBlocks K tx n) 0 (layerPowerSet P n) (zero_mem_layerPowerSet hP n) K
        (selectedRows (fun j ↦ m (π (order j))) K books)
    change DirtyPaper.blockEnergy n (code.encode m) ≤ _ at hh
    simpa only [DirtyPaper.blockEnergy, iidSum, EuclideanSpace.real_norm_sq_eq] using hh
  change (∏ i, (code.messages i : ℝ))⁻¹ * _ ≤ _
  calc
    _ ≤ (∏ i, (code.messages i : ℝ))⁻¹ * ∑ _m : (i : Fin K) → Fin (code.messages i),
        (n : ℝ) * P := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun m _ ↦ hm m))
          (inv_nonneg.mpr (Finset.prod_nonneg (fun _ _ ↦ Nat.cast_nonneg _)))
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_messages,
        ← mul_assoc, inv_mul_cancel₀ (messageCountProduct_pos code).ne', one_mul]

end Code

end CapacityAtlas.Gaussian.MIMOBroadcast
