/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.MeasureRandomBinning.SequenceProducts

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical BigOperators

namespace CapacityAtlas.MeasureBinning

variable {S U Y : Type*} [MeasurableSpace S] [MeasurableSpace U] [MeasurableSpace Y]

noncomputable def safeSequenceState (D : ℕ → RejectionStage S U) (initial fallback : S)
    (C : Set S) (n : ℕ) (samples : SequenceSamples (fun i ↦ (D i).Samples) n) : S :=
  if samples ∈ sequenceSuccess initial (fun i ↦ (D i).next) (fun i ↦ (D i).success) n ∧
      sequenceState initial (fun i ↦ (D i).next) n samples ∈ C then
    sequenceState initial (fun i ↦ (D i).next) n samples else fallback

theorem measurable_safeSequenceState (D : ℕ → RejectionStage S U) (initial fallback : S)
    {C : Set S} (hC : MeasurableSet C) (n : ℕ) :
    Measurable (safeSequenceState D initial fallback C n) :=
  Measurable.ite
    ((measurableSet_sequenceSuccess initial (fun i ↦ (D i).measurable_next)
      (fun i ↦ (D i).measurableSet_success) n).inter
        (hC.preimage (measurable_sequenceState initial (fun i ↦ (D i).measurable_next) n)))
    (measurable_sequenceState initial (fun i ↦ (D i).measurable_next) n) measurable_const

theorem safeSequenceState_mem (D : ℕ → RejectionStage S U) (initial fallback : S)
    (C : Set S) (hfallback : fallback ∈ C) (n : ℕ)
    (samples : SequenceSamples (fun i ↦ (D i).Samples) n) :
    safeSequenceState D initial fallback C n samples ∈ C := by
  unfold safeSequenceState
  split_ifs with h
  · exact h.2
  · exact hfallback

noncomputable def sequenceReceiverBound {M : ℕ → Type*} [∀ j, Fintype (M j)]
    (D : ℕ → RejectionStage S U) (initial fallback : S) (C : Set S)
    (W : Kernel S Y) (aux : S → U) (A : Set (U × Y))
    (message : (j : ℕ) → M j) (n : ℕ) (i : Fin n)
    (books : SequenceSamples (fun j ↦ M j → (D j).Samples) n) : ℝ≥0∞ :=
  let samples := selectedRows message n books
  let good := sequenceSuccess initial (fun j ↦ (D j).next) (fun j ↦ (D j).success) n
  let state := sequenceState initial (fun j ↦ (D j).next) n samples
  goodᶜ.indicator (fun _ ↦ 1) samples +
    good.indicator (fun _ ↦ Cᶜ.indicator (fun _ ↦ 1) state) samples +
    good.indicator (fun _ ↦ W state {y | (aux state, y) ∉ A}) samples +
    W (safeSequenceState D initial fallback C n samples)
      {y | ∃ j, j ≠ message i.val ∧
        (sequenceSampleAt n books i j, y) ∈ candidateRowAcceptance A (D i.val).count}

theorem measurable_sequenceReceiverBound {M : ℕ → Type*} [∀ j, Fintype (M j)]
    (D : ℕ → RejectionStage S U) (initial fallback : S) {C : Set S} (hC : MeasurableSet C)
    (W : Kernel S Y) [IsSFiniteKernel W] {aux : S → U} (haux : Measurable aux)
    {A : Set (U × Y)} (hA : MeasurableSet A) (message : (j : ℕ) → M j)
    (n : ℕ) (i : Fin n) :
    Measurable (sequenceReceiverBound D initial fallback C W aux A message n i) := by
  let state := sequenceState initial (fun j ↦ (D j).next) n
  let good := sequenceSuccess initial (fun j ↦ (D j).next) (fun j ↦ (D j).success) n
  have hstate : Measurable state := measurable_sequenceState initial
    (fun j ↦ (D j).measurable_next) n
  have hgood : MeasurableSet good := measurableSet_sequenceSuccess initial
    (fun j ↦ (D j).measurable_next) (fun j ↦ (D j).measurableSet_success) n
  have hm : Measurable (fun s ↦ W s {y | (aux s, y) ∉ A}) :=
    Kernel.measurable_kernel_prodMk_left
      ((hA.preimage ((haux.comp measurable_fst).prodMk measurable_snd)).compl)
  have hfirst : Measurable (fun samples ↦ goodᶜ.indicator (fun _ ↦ (1 : ℝ≥0∞)) samples +
      good.indicator (fun v ↦ Cᶜ.indicator (fun _ ↦ (1 : ℝ≥0∞)) (state v)) samples +
      good.indicator (fun v ↦ W (state v) {y | (aux (state v), y) ∉ A}) samples) :=
    ((measurable_const.indicator hgood.compl).add
      (((measurable_const.indicator hC.compl).comp hstate).indicator hgood)).add
        ((hm.comp hstate).indicator hgood)
  have hsecond : Measurable (fun books : SequenceSamples (fun j ↦ M j → (D j).Samples) n ↦
      W (safeSequenceState D initial fallback C n (selectedRows message n books))
        {y | ∃ j, j ≠ message i.val ∧
          (sequenceSampleAt n books i j, y) ∈ candidateRowAcceptance A (D i.val).count}) := by
    have hevent : MeasurableSet {p : SequenceSamples (fun j ↦ M j → (D j).Samples) n × Y |
        ∃ j, j ≠ message i.val ∧
          (sequenceSampleAt n p.1 i j, p.2) ∈ candidateRowAcceptance A (D i.val).count} := by
      simp only [setOf_exists]
      apply MeasurableSet.iUnion
      intro j
      apply MeasurableSet.inter (MeasurableSet.const _)
      exact (measurableSet_candidateRowAcceptance hA _).preimage
          (((measurable_pi_apply j).comp ((measurable_sequenceSampleAt n i).comp measurable_fst)).prodMk
            measurable_snd)
    exact Kernel.measurable_kernel_prodMk_left
      (κ := W.comap (fun books ↦ safeSequenceState D initial fallback C n
        (selectedRows message n books))
          ((measurable_safeSequenceState D initial fallback hC n).comp
            (measurable_selectedRows message n))) hevent
  exact (hfirst.comp (measurable_selectedRows message n)).add hsecond

theorem sequenceReceiver_error_le {M : ℕ → Type*} [∀ j, Fintype (M j)]
    [∀ j, Nonempty (M j)] [∀ j, MeasurableSpace (M j)]
    (D : ℕ → RejectionStage S U) (initial fallback : S) (C : Set S)
    (W : Kernel S Y) [IsMarkovKernel W] (aux : S → U) (A : Set (U × Y))
    (message : (j : ℕ) → M j) (n : ℕ) (i : Fin n) [Nonempty (Fin (D i.val).count)]
    (hread : ∀ samples ∈ sequenceSuccess initial (fun j ↦ (D j).next)
      (fun j ↦ (D j).success) n, ∃ l, (sequenceSampleAt n samples i l).1 =
        aux (sequenceState initial (fun j ↦ (D j).next) n samples))
    (books : SequenceSamples (fun j ↦ M j → (D j).Samples) n) :
    W (safeSequenceState D initial fallback C n (selectedRows message n books))
      {y | binningDecoder A (fun j l ↦ (sequenceSampleAt n books i j l).1) y ≠ message i.val} ≤
        sequenceReceiverBound D initial fallback C W aux A message n i books := by
  let samples := selectedRows message n books
  let good := sequenceSuccess initial (fun j ↦ (D j).next) (fun j ↦ (D j).success) n
  let state := sequenceState initial (fun j ↦ (D j).next) n samples
  by_cases hs : samples ∈ good
  · by_cases hc : state ∈ C
    · have hsafe : safeSequenceState D initial fallback C n samples = state := by
        exact if_pos ⟨hs, hc⟩
      have hbound : W state
          {y | binningDecoder A (fun j l ↦ (sequenceSampleAt n books i j l).1) y ≠ message i.val} ≤
          W state {y | (aux state, y) ∉ A} + W state
            {y | ∃ j, j ≠ message i.val ∧
              (sequenceSampleAt n books i j, y) ∈ candidateRowAcceptance A (D i.val).count} := by
        apply (measure_mono (t := {y | (aux state, y) ∉ A} ∪
          {y | ∃ j, j ≠ message i.val ∧
            (sequenceSampleAt n books i j, y) ∈ candidateRowAcceptance A (D i.val).count}) ?_).trans
          (measure_union_le _ _)
        intro y hy
        by_cases ha : (aux state, y) ∈ A
        · right
          by_contra hnone
          apply hy
          apply binningDecoder_eq_of_accepts A _ _ _
          · obtain ⟨l, hl⟩ := hread samples hs
            refine ⟨l, ?_⟩
            have hrow : sequenceSampleAt n samples i = sequenceSampleAt n books i (message i.val) :=
              sequenceSampleAt_selectedRows message n books i
            rw [hrow] at hl
            rwa [hl]
          · intro j hj l hl
            exact hnone ⟨j, hj, l, hl⟩
        · exact Or.inl ha
      simpa [sequenceReceiverBound, safeSequenceState, samples, good, state, hs, hc] using hbound
    · apply le_trans prob_le_one
      simp [sequenceReceiverBound, samples, good, state, hs, hc]
      exact (le_add_right le_rfl).trans (le_add_right le_rfl)
  · apply le_trans prob_le_one
    simp [sequenceReceiverBound, samples, good, hs]

theorem lintegral_sequenceReceiverBound_le {M : ℕ → Type*} [∀ j, Fintype (M j)]
    (D : ℕ → RejectionStage S U) (initial fallback : S) {C : Set S} (hC : MeasurableSet C)
    (W : Kernel S Y) [IsMarkovKernel W] {aux : S → U} (haux : Measurable aux)
    {A : Set (U × Y)} (hA : MeasurableSet A) (message : (j : ℕ) → M j)
    (n : ℕ) (i : Fin n) {c : ℝ≥0∞}
    (huniform : ∀ y, (D i.val).candidate {u | (u, y) ∈ A} ≤ c) :
    (∫⁻ books, sequenceReceiverBound D initial fallback C W aux A message n i books
      ∂sequenceSampleLaw (fun j ↦ Measure.pi (fun _ : M j ↦ (D j).sampleLaw)) n) ≤
      sequenceSampleLaw (fun j ↦ (D j).sampleLaw) n
        (sequenceSuccess initial (fun j ↦ (D j).next) (fun j ↦ (D j).success) n)ᶜ +
      (2 : ℝ≥0∞) ^ n * sequenceReferenceLaw (fun j ↦ (D j).referenceKernel) initial n Cᶜ +
      (2 : ℝ≥0∞) ^ n * ((sequenceReferenceLaw (fun j ↦ (D j).referenceKernel) initial n) ⊗ₘ W)
        {p | (aux p.1, p.2) ∉ A} +
      (Fintype.card (M i.val) - 1 : ℕ) * (D i.val).count * c := by
  let state := sequenceState initial (fun j ↦ (D j).next) n
  let good := sequenceSuccess initial (fun j ↦ (D j).next) (fun j ↦ (D j).success) n
  let ν := sequenceSampleLaw (fun j ↦ (D j).sampleLaw) n
  let booksLaw := sequenceSampleLaw (fun j ↦ Measure.pi (fun _ : M j ↦ (D j).sampleLaw)) n
  let f₀ : SequenceSamples (fun j ↦ (D j).Samples) n → ℝ≥0∞ := goodᶜ.indicator (fun _ ↦ 1)
  let f₁ : SequenceSamples (fun j ↦ (D j).Samples) n → ℝ≥0∞ :=
    good.indicator (fun v ↦ Cᶜ.indicator (fun _ ↦ 1) (state v))
  let f₂ : SequenceSamples (fun j ↦ (D j).Samples) n → ℝ≥0∞ :=
    good.indicator (fun v ↦ W (state v) {y | (aux (state v), y) ∉ A})
  let ρ := W.comap (safeSequenceState D initial fallback C n)
    (measurable_safeSequenceState D initial fallback hC n)
  let f₃ : SequenceSamples (fun j ↦ M j → (D j).Samples) n → ℝ≥0∞ := fun books ↦
    ρ (selectedRows message n books)
      {y | ∃ j, j ≠ message i.val ∧
        (sequenceSampleAt n books i j, y) ∈ candidateRowAcceptance A (D i.val).count}
  have hstate : Measurable state := measurable_sequenceState initial
    (fun j ↦ (D j).measurable_next) n
  have hgood : MeasurableSet good := measurableSet_sequenceSuccess initial
    (fun j ↦ (D j).measurable_next) (fun j ↦ (D j).measurableSet_success) n
  have hE : MeasurableSet {p : S × Y | (aux p.1, p.2) ∉ A} :=
    (hA.preimage ((haux.comp measurable_fst).prodMk measurable_snd)).compl
  have hm : Measurable (fun s ↦ W s {y | (aux s, y) ∉ A}) :=
    Kernel.measurable_kernel_prodMk_left hE
  have hf₀ : Measurable f₀ := measurable_const.indicator hgood.compl
  have hf₁ : Measurable f₁ :=
    ((measurable_const.indicator hC.compl).comp hstate).indicator hgood
  have hf₂ : Measurable f₂ := (hm.comp hstate).indicator hgood
  have hmp := measurePreserving_selectedRows (fun j ↦ (D j).sampleLaw) message n
  have hb₀ : (∫⁻ books, f₀ (selectedRows message n books) ∂booksLaw) = ν goodᶜ := by
    rw [hmp.lintegral_comp hf₀]
    simp [f₀, lintegral_indicator hgood.compl]
    rfl
  have hb₁ : (∫⁻ books, f₁ (selectedRows message n books) ∂booksLaw) ≤
      (2 : ℝ≥0∞) ^ n * sequenceReferenceLaw (fun j ↦ (D j).referenceKernel) initial n Cᶜ := by
    rw [hmp.lintegral_comp hf₁]
    change (∫⁻ samples, good.indicator (fun v ↦ Cᶜ.indicator (fun _ ↦ 1) (state v)) samples ∂ν) ≤ _
    rw [lintegral_indicator hgood]
    have hb := lintegral_rejectionSequence_success_le D initial n
      (f := Cᶜ.indicator (fun _ ↦ 1))
      (measurable_const.indicator hC.compl)
    simpa [lintegral_indicator hC.compl] using hb
  have hb₂ : (∫⁻ books, f₂ (selectedRows message n books) ∂booksLaw) ≤
      (2 : ℝ≥0∞) ^ n * ((sequenceReferenceLaw (fun j ↦ (D j).referenceKernel) initial n) ⊗ₘ W)
        {p | (aux p.1, p.2) ∉ A} := by
    rw [hmp.lintegral_comp hf₂]
    change (∫⁻ samples, good.indicator (fun v ↦ W (state v) {y | (aux (state v), y) ∉ A})
      samples ∂ν) ≤ _
    rw [lintegral_indicator hgood]
    exact rejectionSequence_success_badOutput_le D initial n W hE
  have hb₃ : (∫⁻ books, f₃ books ∂booksLaw) ≤
      (Fintype.card (M i.val) - 1 : ℕ) * (D i.val).count * c := by
    have hb := lintegral_sequence_competingBins_le (fun j ↦ (D j).sampleLaw)
      message n i ρ (measurableSet_candidateRowAcceptance hA _)
        (candidateRowAcceptance_mass_le (D i.val).candidate hA huniform (D i.val).count)
    simpa only [mul_assoc] using hb
  change (∫⁻ books, f₀ (selectedRows message n books) + f₁ (selectedRows message n books) +
    f₂ (selectedRows message n books) + f₃ books ∂booksLaw) ≤ _
  rw [lintegral_add_left (show Measurable (fun books ↦
      f₀ (selectedRows message n books) + f₁ (selectedRows message n books) +
        f₂ (selectedRows message n books)) from ((hf₀.add hf₁).add hf₂).comp hmp.measurable),
    lintegral_add_left (show Measurable (fun books ↦
      f₀ (selectedRows message n books) + f₁ (selectedRows message n books)) from
        (hf₀.add hf₁).comp hmp.measurable),
    lintegral_add_left (show Measurable (fun books ↦ f₀ (selectedRows message n books)) from
      hf₀.comp hmp.measurable), hb₀]
  exact add_le_add (add_le_add (add_le_add le_rfl hb₁) hb₂) hb₃

theorem exists_sequenceBooks_jointBound_le
    {M : ℕ → Type*} [∀ j, Fintype (M j)] {J : Type*} [Fintype J] [Nonempty J]
    (D : ℕ → RejectionStage S U) (initial fallback : S) {C : Set S} (hC : MeasurableSet C)
    (n : ℕ) {Y : Fin n → Type*} [∀ i, MeasurableSpace (Y i)]
    (W : (i : Fin n) → Kernel S (Y i)) [∀ i, IsMarkovKernel (W i)]
    (aux : Fin n → S → U) (haux : ∀ i, Measurable (aux i))
    (A : (i : Fin n) → Set (U × Y i)) (hA : ∀ i, MeasurableSet (A i))
    (message : J → (j : ℕ) → M j) (c : Fin n → ℝ≥0∞)
    (huniform : ∀ i y, (D i.val).candidate {u | (u, y) ∈ A i} ≤ c i) :
    ∃ books : SequenceSamples (fun j ↦ M j → (D j).Samples) n,
      (Fintype.card J : ℝ≥0∞)⁻¹ * ∑ m : J, ∑ i : Fin n,
        sequenceReceiverBound D initial fallback C (W i) (aux i) (A i) (message m) n i books ≤
      ∑ i : Fin n,
        (sequenceSampleLaw (fun j ↦ (D j).sampleLaw) n
          (sequenceSuccess initial (fun j ↦ (D j).next) (fun j ↦ (D j).success) n)ᶜ +
        (2 : ℝ≥0∞) ^ n * sequenceReferenceLaw (fun j ↦ (D j).referenceKernel) initial n Cᶜ +
        (2 : ℝ≥0∞) ^ n * ((sequenceReferenceLaw (fun j ↦ (D j).referenceKernel) initial n) ⊗ₘ W i)
          {p | (aux i p.1, p.2) ∉ A i} +
        (Fintype.card (M i.val) - 1 : ℕ) * (D i.val).count * c i) := by
  let μ := sequenceSampleLaw (fun j ↦ Measure.pi (fun _ : M j ↦ (D j).sampleLaw)) n
  let B (m : J) (i : Fin n) :=
    sequenceReceiverBound D initial fallback C (W i) (aux i) (A i) (message m) n i
  have hB (m : J) (i : Fin n) : Measurable (B m i) :=
    measurable_sequenceReceiverBound D initial fallback hC (W i) (haux i) (hA i) (message m) n i
  have hsum : Measurable (fun books ↦ (Fintype.card J : ℝ≥0∞)⁻¹ *
      ∑ m : J, ∑ i : Fin n, B m i books) :=
    measurable_const.mul (Finset.measurable_sum _ (fun m _ ↦
      Finset.measurable_sum _ (fun i _ ↦ hB m i)))
  obtain ⟨books, hbooks⟩ := exists_le_lintegral (μ := μ) hsum.aemeasurable
  refine ⟨books, hbooks.trans ?_⟩
  rw [lintegral_const_mul _ (Finset.measurable_sum _ (fun m _ ↦
    Finset.measurable_sum _ (fun i _ ↦ hB m i))),
    lintegral_finsetSum _ (fun m _ ↦ Finset.measurable_sum _ (fun i _ ↦ hB m i))]
  simp_rw [lintegral_finsetSum _ (fun i _ ↦ hB _ i)]
  calc
    _ ≤ (Fintype.card J : ℝ≥0∞)⁻¹ * ∑ _m : J, ∑ i : Fin n,
        (sequenceSampleLaw (fun j ↦ (D j).sampleLaw) n
          (sequenceSuccess initial (fun j ↦ (D j).next) (fun j ↦ (D j).success) n)ᶜ +
        (2 : ℝ≥0∞) ^ n * sequenceReferenceLaw (fun j ↦ (D j).referenceKernel) initial n Cᶜ +
        (2 : ℝ≥0∞) ^ n * ((sequenceReferenceLaw (fun j ↦ (D j).referenceKernel) initial n) ⊗ₘ W i)
          {p | (aux i p.1, p.2) ∉ A i} +
        (Fintype.card (M i.val) - 1 : ℕ) * (D i.val).count * c i) := by
      gcongr with m _ i _
      exact lintegral_sequenceReceiverBound_le D initial fallback hC (W i) (haux i) (hA i)
        (message m) n i (huniform i)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
        ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
        one_mul]

end CapacityAtlas.MeasureBinning
