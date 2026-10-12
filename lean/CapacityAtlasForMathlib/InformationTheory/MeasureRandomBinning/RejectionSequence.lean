/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.MeasureRandomBinning.SampledSequence

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical BigOperators

namespace CapacityAtlas.MeasureBinning

variable {S U : Type*} [MeasurableSpace S] [MeasurableSpace U]

noncomputable def updateKernel (η : Kernel S U) [IsSFiniteKernel η]
    {update : S × U → S} (hupdate : Measurable update) : Kernel S S where
  toFun s := (η s).map (fun u ↦ update (s, u))
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro E hE
    change Measurable (fun s ↦ (η s).map (fun u ↦ update (s, u)) E)
    have heq (s : S) : (η s).map (fun u ↦ update (s, u)) E =
        η s {u | update (s, u) ∈ E} :=
      Measure.map_apply (show Measurable (fun u ↦ update (s, u)) from
        hupdate.comp measurable_prodMk_left) hE
    simp_rw [heq]
    exact Kernel.measurable_kernel_prodMk_left (hE.preimage hupdate)

theorem updateKernel_apply (η : Kernel S U) [IsSFiniteKernel η]
    {update : S × U → S} (hupdate : Measurable update) (s : S) :
    updateKernel η hupdate s = (η s).map (fun u ↦ update (s, u)) := rfl

instance (η : Kernel S U) [IsMarkovKernel η]
    {update : S × U → S} (hupdate : Measurable update) :
    IsMarkovKernel (updateKernel η hupdate) where
  isProbabilityMeasure s := by
    rw [updateKernel_apply]
    exact Measure.isProbabilityMeasure_map (hupdate.comp measurable_prodMk_left).aemeasurable

structure RejectionStage (S U : Type*) [MeasurableSpace S] [MeasurableSpace U] where
  target : Kernel S U
  target_markov : IsMarkovKernel target
  candidate : Measure U
  candidate_probability : IsProbabilityMeasure candidate
  density : S × U → ℝ≥0∞
  measurable_density : Measurable density
  target_eq_density : ∀ s, target s = candidate.withDensity (fun u ↦ density (s, u))
  good : Set (S × U)
  measurable_good : MeasurableSet good
  threshold : ℝ
  threshold_pos : 0 < threshold
  density_le : ∀ z ∈ good, density z ≤ ENNReal.ofReal threshold
  update : S × U → S
  measurable_update : Measurable update
  fallback : U × ℝ
  count : ℕ

namespace RejectionStage

variable (D : RejectionStage S U)

instance : IsMarkovKernel D.target := D.target_markov
instance : IsProbabilityMeasure D.candidate := D.candidate_probability

abbrev Samples := Fin D.count → U × ℝ

noncomputable def sampleLaw : Measure D.Samples :=
  Measure.pi (fun _ : Fin D.count ↦ D.candidate.prod seedLaw)

instance : IsProbabilityMeasure D.sampleLaw := by unfold sampleLaw; infer_instance

noncomputable def next (p : S × D.Samples) : S :=
  D.update (p.1, (firstHit
    (seededAcceptance (fun u ↦ D.density (p.1, u)) {u | (p.1, u) ∈ D.good} D.threshold)
      D.fallback D.count p.2).1)

def success : Set (S × D.Samples) :=
  {p | p.1 ∈ goodState D.target D.good ∧
    hasHit (seededAcceptance (fun u ↦ D.density (p.1, u))
      {u | (p.1, u) ∈ D.good} D.threshold) p.2}

theorem measurable_next : Measurable D.next :=
  D.measurable_update.comp (measurable_fst.prodMk
    (measurable_firstHit_section
      (measurableSet_seededAcceptanceSection D.measurable_density D.measurable_good D.threshold)
        D.fallback D.count).fst)

theorem measurableSet_success : MeasurableSet D.success :=
  ((measurableSet_goodState D.target D.measurable_good).preimage measurable_fst).inter
    (measurableSet_hasHit_section
      (measurableSet_seededAcceptanceSection D.measurable_density D.measurable_good D.threshold)
        D.count)

noncomputable def referenceKernel : Kernel S S := updateKernel D.target D.measurable_update

instance : IsMarkovKernel D.referenceKernel := by unfold referenceKernel; infer_instance

theorem sampledKernel_eq_rejection_map (s : S) :
    sampledKernel D.sampleLaw D.measurableSet_success D.measurable_next s =
      (rejectionKernel D.target D.candidate D.measurable_density D.measurable_good
        D.threshold D.fallback D.count s).map (fun u ↦ D.update (s, u)) := by
  ext E hE
  have hu : Measurable (fun u ↦ D.update (s, u)) := D.measurable_update.comp measurable_prodMk_left
  rw [sampledKernel_apply D.sampleLaw D.measurableSet_success D.measurable_next s hE,
    Measure.map_apply hu hE, rejectionKernel, Kernel.piecewise_apply']
  by_cases hs : s ∈ goodState D.target D.good
  · rw [if_pos hs, seededFirstHitKernel_apply D.candidate D.measurable_density D.measurable_good
      D.threshold D.fallback D.count s (hE.preimage hu)]
    congr 1
    ext book
    simp only [success, mem_setOf_eq, hs, true_and, firstHitEvent, mem_preimage, next]
  · rw [if_neg hs]
    simp [success, hs]

theorem sampledKernel_le (s : S) :
    sampledKernel D.sampleLaw D.measurableSet_success D.measurable_next s ≤
      (2 : ℝ≥0∞) • D.referenceKernel s := by
  rw [sampledKernel_eq_rejection_map]
  have hu : Measurable (fun u ↦ D.update (s, u)) := D.measurable_update.comp measurable_prodMk_left
  calc
    _ ≤ ((2 : ℝ≥0∞) • D.target s).map (fun u ↦ D.update (s, u)) :=
      Measure.map_mono (rejectionKernel_le_two D.target D.candidate D.measurable_density
        D.target_eq_density D.measurable_good D.threshold_pos D.density_le D.fallback D.count s) hu
    _ = _ := by rw [Measure.map_smul]; rfl

theorem sample_failure_eq (s : S) :
    D.sampleLaw {v | (s, v) ∉ D.success} =
      rejectionFailure D.target D.candidate D.density D.good D.threshold D.count s := by
  by_cases hs : s ∈ goodState D.target D.good
  · simp only [success, mem_setOf_eq, hs, true_and, rejectionFailure, if_pos]
    rfl
  · simp [success, hs, rejectionFailure]

noncomputable def failureBound (σ : Measure S) : ℝ≥0∞ :=
  2 * (σ ⊗ₘ D.target) D.goodᶜ +
    ENNReal.ofReal (Real.exp (-((D.count : ℝ) * ((1 / 2) / D.threshold))))

theorem lintegral_failure_le (σ : Measure S) [IsProbabilityMeasure σ] :
    (∫⁻ s, D.sampleLaw {v | (s, v) ∉ D.success} ∂σ) ≤ D.failureBound σ := by
  simp_rw [sample_failure_eq]
  exact lintegral_rejectionFailure_le σ D.target D.candidate D.measurable_density
    D.target_eq_density D.measurable_good D.threshold_pos D.density_le D.count

end RejectionStage

theorem rejectionSequence_successLaw_le (D : ℕ → RejectionStage S U) (initial : S) (n : ℕ) :
    sequenceSuccessLaw (fun i ↦ (D i).sampleLaw) initial (fun i ↦ (D i).next)
        (fun i ↦ (D i).success) n ≤
      (2 : ℝ≥0∞) ^ n • sequenceReferenceLaw (fun i ↦ (D i).referenceKernel) initial n :=
  sequenceSuccessLaw_le (fun i ↦ (D i).sampleLaw) initial (fun i ↦ (D i).measurable_next)
    (fun i ↦ (D i).measurableSet_success) (fun i ↦ (D i).referenceKernel)
    (fun i ↦ (D i).sampledKernel_le) n

theorem rejectionSequence_failure_le (D : ℕ → RejectionStage S U) (initial : S) (n : ℕ) :
    sequenceSampleLaw (fun i ↦ (D i).sampleLaw) n
        (sequenceSuccess initial (fun i ↦ (D i).next) (fun i ↦ (D i).success) n)ᶜ ≤
      ∑ i ∈ Finset.range n, (2 : ℝ≥0∞) ^ i *
        (D i).failureBound (sequenceReferenceLaw (fun j ↦ (D j).referenceKernel) initial i) :=
  sequenceFailure_le_sum (fun i ↦ (D i).sampleLaw) initial (fun i ↦ (D i).measurable_next)
    (fun i ↦ (D i).measurableSet_success) (fun i ↦ (D i).referenceKernel)
    (fun i ↦ (D i).sampledKernel_le) _ (fun i ↦ (D i).lintegral_failure_le _) n

theorem lintegral_rejectionSequence_success_le (D : ℕ → RejectionStage S U)
    (initial : S) (n : ℕ) {f : S → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ samples in sequenceSuccess initial (fun i ↦ (D i).next) (fun i ↦ (D i).success) n,
      f (sequenceState initial (fun i ↦ (D i).next) n samples)
      ∂sequenceSampleLaw (fun i ↦ (D i).sampleLaw) n) ≤
        (2 : ℝ≥0∞) ^ n * ∫⁻ s, f s
          ∂sequenceReferenceLaw (fun i ↦ (D i).referenceKernel) initial n := by
  rw [← lintegral_map hf (measurable_sequenceState initial (fun i ↦ (D i).measurable_next) n)]
  change (∫⁻ s, f s ∂sequenceSuccessLaw (fun i ↦ (D i).sampleLaw) initial
    (fun i ↦ (D i).next) (fun i ↦ (D i).success) n) ≤ _
  calc
    _ ≤ ∫⁻ s, f s ∂((2 : ℝ≥0∞) ^ n •
        sequenceReferenceLaw (fun i ↦ (D i).referenceKernel) initial n) :=
      lintegral_mono' (rejectionSequence_successLaw_le D initial n) le_rfl
    _ = _ := lintegral_smul_measure _ _

theorem rejectionSequence_success_badOutput_le {Y : Type*} [MeasurableSpace Y]
    (D : ℕ → RejectionStage S U) (initial : S) (n : ℕ)
    (W : Kernel S Y) [IsSFiniteKernel W] {E : Set (S × Y)} (hE : MeasurableSet E) :
    (∫⁻ samples in sequenceSuccess initial (fun i ↦ (D i).next) (fun i ↦ (D i).success) n,
      W (sequenceState initial (fun i ↦ (D i).next) n samples)
        {y | (sequenceState initial (fun i ↦ (D i).next) n samples, y) ∈ E}
      ∂sequenceSampleLaw (fun i ↦ (D i).sampleLaw) n) ≤
        (2 : ℝ≥0∞) ^ n *
          (sequenceReferenceLaw (fun i ↦ (D i).referenceKernel) initial n ⊗ₘ W) E := by
  rw [Measure.compProd_apply hE]
  exact lintegral_rejectionSequence_success_le D initial n
    (Kernel.measurable_kernel_prodMk_left hE)

end CapacityAtlas.MeasureBinning
