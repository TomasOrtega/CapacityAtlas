/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.MeasureRandomBinning.LayerRejection

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical BigOperators

namespace CapacityAtlas.MeasureBinning

universe v

variable {S V : Type*} [MeasurableSpace S] [MeasurableSpace V]

noncomputable def sampledKernel (ν : Measure V) [SFinite ν]
    {A : Set (S × V)} (hA : MeasurableSet A) {next : S × V → S}
    (hnext : Measurable next) : Kernel S S where
  toFun s := (ν.restrict {v | (s, v) ∈ A}).map (fun v ↦ next (s, v))
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro E hE
    have heq (s : S) :
        (ν.restrict {v | (s, v) ∈ A}).map (fun v ↦ next (s, v)) E =
          ν {v | (s, v) ∈ A ∧ next (s, v) ∈ E} := by
      have hn : Measurable (fun v ↦ next (s, v)) := hnext.comp measurable_prodMk_left
      rw [Measure.map_apply hn hE, Measure.restrict_apply (hE.preimage hn)]
      congr 1
      ext v
      exact and_comm
    change Measurable (fun s : S ↦
      (ν.restrict {v | (s, v) ∈ A}).map (fun v ↦ next (s, v)) E)
    simp_rw [heq]
    exact measurable_measure_prodMk_left (hA.inter (hE.preimage hnext))

theorem sampledKernel_apply (ν : Measure V) [SFinite ν]
    {A : Set (S × V)} (hA : MeasurableSet A) {next : S × V → S}
    (hnext : Measurable next) (s : S) {E : Set S} (hE : MeasurableSet E) :
    sampledKernel ν hA hnext s E = ν {v | (s, v) ∈ A ∧ next (s, v) ∈ E} := by
  change (ν.restrict {v | (s, v) ∈ A}).map (fun v ↦ next (s, v)) E = _
  have hn : Measurable (fun v ↦ next (s, v)) := hnext.comp measurable_prodMk_left
  rw [Measure.map_apply hn hE, Measure.restrict_apply (hE.preimage hn)]
  congr 1
  ext v
  exact and_comm

instance (ν : Measure V) [IsProbabilityMeasure ν]
    {A : Set (S × V)} (hA : MeasurableSet A) {next : S × V → S}
    (hnext : Measurable next) : IsFiniteKernel (sampledKernel ν hA hnext) where
  exists_univ_le := ⟨1, ENNReal.one_lt_top, fun s ↦ by
    rw [sampledKernel_apply ν hA hnext s MeasurableSet.univ]
    exact prob_le_one⟩

theorem sampledKernel_univ_add_failure (ν : Measure V) [IsProbabilityMeasure ν]
    {A : Set (S × V)} (hA : MeasurableSet A) {next : S × V → S}
    (hnext : Measurable next) (s : S) :
    sampledKernel ν hA hnext s univ + ν {v | (s, v) ∉ A} = 1 := by
  rw [sampledKernel_apply ν hA hnext s MeasurableSet.univ]
  simp only [mem_univ, and_true]
  change ν {v | (s, v) ∈ A} + ν ({v | (s, v) ∈ A}ᶜ) = 1
  exact (measure_add_measure_compl (hA.preimage measurable_prodMk_left)).trans (measure_univ : ν univ = 1)

theorem sampledKernel_comp_eq_actual {Ω : Type*} [MeasurableSpace Ω]
    (π : Measure Ω) [IsProbabilityMeasure π] (ν : Measure V) [IsProbabilityMeasure ν]
    {C : Set Ω} (hC : MeasurableSet C) {state : Ω → S} (hstate : Measurable state)
    {A : Set (S × V)} (hA : MeasurableSet A) {next : S × V → S}
    (hnext : Measurable next) :
    sampledKernel ν hA hnext ∘ₘ (π.restrict C).map state =
      ((π.prod ν).restrict {p | p.1 ∈ C ∧ (state p.1, p.2) ∈ A}).map
        (fun p ↦ next (state p.1, p.2)) := by
  ext E hE
  have hpair : Measurable (fun p : Ω × V ↦ (state p.1, p.2)) :=
    (hstate.comp measurable_fst).prodMk measurable_snd
  have hm : Measurable (fun s ↦ ν {v | (s, v) ∈ A ∧ next (s, v) ∈ E}) :=
    measurable_measure_prodMk_left (hA.inter (hE.preimage hnext))
  have hn : Measurable (fun p : Ω × V ↦ next (state p.1, p.2)) := hnext.comp hpair
  have hsuccess : MeasurableSet {p : Ω × V | p.1 ∈ C ∧ (state p.1, p.2) ∈ A} :=
    (hC.preimage measurable_fst).inter (hA.preimage hpair)
  rw [Measure.bind_apply hE (sampledKernel ν hA hnext).aemeasurable]
  simp_rw [sampledKernel_apply ν hA hnext _ hE]
  rw [lintegral_map hm hstate, Measure.map_apply hn hE,
    Measure.restrict_apply (hE.preimage hn),
    Measure.prod_apply ((hE.preimage hn).inter hsuccess), ← lintegral_indicator hC]
  apply lintegral_congr
  intro ω
  by_cases hω : ω ∈ C
  · rw [indicator_of_mem hω]
    congr 1
    ext v
    simp only [mem_inter_iff, mem_preimage, mem_setOf_eq, hω, true_and]
    exact and_comm
  · rw [indicator_of_notMem hω]
    have hempty : {v | (ω, v) ∈
        (fun p : Ω × V ↦ next (state p.1, p.2)) ⁻¹' E ∩
          {p | p.1 ∈ C ∧ (state p.1, p.2) ∈ A}} = ∅ := by
      ext v
      simp [hω]
    exact ((congrArg ν hempty).trans measure_empty).symm

@[reducible]
def SequenceSamples (V : ℕ → Type v) : ℕ → Type v
  | 0 => PUnit
  | n + 1 => SequenceSamples V n × V n
termination_by structural n => n

@[reducible]
instance sequenceSamplesMeasurableSpace (V : ℕ → Type v) [∀ n, MeasurableSpace (V n)] :
    (n : ℕ) → MeasurableSpace (SequenceSamples V n)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | n + 1 => @Prod.instMeasurableSpace (SequenceSamples V n) (V n)
      (sequenceSamplesMeasurableSpace V n) (inferInstanceAs (MeasurableSpace (V n)))
termination_by structural n => n

noncomputable def sequenceSampleLaw {V : ℕ → Type*} [∀ n, MeasurableSpace (V n)]
    (ν : (n : ℕ) → Measure (V n)) : (n : ℕ) → Measure (SequenceSamples V n)
  | 0 => Measure.dirac PUnit.unit
  | n + 1 => (sequenceSampleLaw ν n).prod (ν n)

instance sequenceSampleLawProbability {V : ℕ → Type*} [∀ n, MeasurableSpace (V n)]
    (ν : (n : ℕ) → Measure (V n)) [∀ n, IsProbabilityMeasure (ν n)] :
    (n : ℕ) → IsProbabilityMeasure (sequenceSampleLaw ν n)
  | 0 => inferInstanceAs (IsProbabilityMeasure (Measure.dirac PUnit.unit))
  | n + 1 => by
      change IsProbabilityMeasure ((sequenceSampleLaw ν n).prod (ν n))
      letI := sequenceSampleLawProbability ν n
      infer_instance

def sequenceState {V : ℕ → Type*} (initial : S) (next : (n : ℕ) → S × V n → S) :
    (n : ℕ) → SequenceSamples V n → S
  | 0, _ => initial
  | n + 1, samples => next n (sequenceState initial next n samples.1, samples.2)

def sequenceSuccess {V : ℕ → Type*} (initial : S) (next : (n : ℕ) → S × V n → S)
    (A : (n : ℕ) → Set (S × V n)) : (n : ℕ) → Set (SequenceSamples V n)
  | 0 => univ
  | n + 1 => {samples | samples.1 ∈ sequenceSuccess initial next A n ∧
      (sequenceState initial next n samples.1, samples.2) ∈ A n}

theorem measurable_sequenceState {V : ℕ → Type*} [∀ n, MeasurableSpace (V n)]
    (initial : S) {next : (n : ℕ) → S × V n → S} (hnext : ∀ n, Measurable (next n)) :
    ∀ n, Measurable (sequenceState initial next n)
  | 0 => measurable_const
  | n + 1 => (hnext n).comp
      (((measurable_sequenceState initial hnext n).comp measurable_fst).prodMk measurable_snd)

theorem measurableSet_sequenceSuccess {V : ℕ → Type*} [∀ n, MeasurableSpace (V n)]
    (initial : S) {next : (n : ℕ) → S × V n → S} (hnext : ∀ n, Measurable (next n))
    {A : (n : ℕ) → Set (S × V n)} (hA : ∀ n, MeasurableSet (A n)) :
    ∀ n, MeasurableSet (sequenceSuccess initial next A n)
  | 0 => MeasurableSet.univ
  | n + 1 => ((measurableSet_sequenceSuccess initial hnext hA n).preimage measurable_fst).inter
      ((hA n).preimage (((measurable_sequenceState initial hnext n).comp measurable_fst).prodMk
        measurable_snd))

noncomputable def sequenceSuccessLaw {V : ℕ → Type*} [∀ n, MeasurableSpace (V n)]
    (ν : (n : ℕ) → Measure (V n)) (initial : S) (next : (n : ℕ) → S × V n → S)
    (A : (n : ℕ) → Set (S × V n)) (n : ℕ) : Measure S :=
  ((sequenceSampleLaw ν n).restrict (sequenceSuccess initial next A n)).map
    (sequenceState initial next n)

instance {V : ℕ → Type*} [∀ n, MeasurableSpace (V n)]
    (ν : (n : ℕ) → Measure (V n)) [∀ n, IsProbabilityMeasure (ν n)]
    (initial : S) (next : (n : ℕ) → S × V n → S) (A : (n : ℕ) → Set (S × V n)) (n : ℕ) :
    IsFiniteMeasure (sequenceSuccessLaw ν initial next A n) := by
  unfold sequenceSuccessLaw
  infer_instance

theorem sequenceSuccessLaw_succ {V : ℕ → Type*} [∀ n, MeasurableSpace (V n)]
    (ν : (n : ℕ) → Measure (V n)) [∀ n, IsProbabilityMeasure (ν n)]
    (initial : S) {next : (n : ℕ) → S × V n → S} (hnext : ∀ n, Measurable (next n))
    {A : (n : ℕ) → Set (S × V n)} (hA : ∀ n, MeasurableSet (A n)) (n : ℕ) :
    sequenceSuccessLaw ν initial next A (n + 1) =
      sampledKernel (ν n) (hA n) (hnext n) ∘ₘ sequenceSuccessLaw ν initial next A n :=
  (sampledKernel_comp_eq_actual (sequenceSampleLaw ν n) (ν n)
    (measurableSet_sequenceSuccess initial hnext hA n) (measurable_sequenceState initial hnext n)
      (hA n) (hnext n)).symm

theorem sequenceSuccessLaw_zero {V : ℕ → Type*} [∀ n, MeasurableSpace (V n)]
    (ν : (n : ℕ) → Measure (V n)) (initial : S) (next : (n : ℕ) → S × V n → S)
    (A : (n : ℕ) → Set (S × V n)) :
    sequenceSuccessLaw ν initial next A 0 = Measure.dirac initial := by
  change ((Measure.dirac (PUnit.unit : SequenceSamples V 0)).restrict univ).map
    (fun _ ↦ initial) = _
  rw [Measure.restrict_univ, Measure.map_dirac' measurable_const]

noncomputable def sequenceReferenceLaw (κ : ℕ → Kernel S S) (initial : S) : ℕ → Measure S
  | 0 => Measure.dirac initial
  | n + 1 => κ n ∘ₘ sequenceReferenceLaw κ initial n

instance sequenceReferenceLawProbability (κ : ℕ → Kernel S S) [∀ n, IsMarkovKernel (κ n)]
    (initial : S) : (n : ℕ) → IsProbabilityMeasure (sequenceReferenceLaw κ initial n)
  | 0 => inferInstanceAs (IsProbabilityMeasure (Measure.dirac initial))
  | n + 1 => by
      change IsProbabilityMeasure (κ n ∘ₘ sequenceReferenceLaw κ initial n)
      letI := sequenceReferenceLawProbability κ initial n
      infer_instance

theorem comp_le_mul_of_row_le (ψ σ : Measure S) (κ η : Kernel S S) (C D : ℝ≥0∞)
    (hprefix : ψ ≤ C • σ) (hrow : ∀ s, κ s ≤ D • η s) :
    κ ∘ₘ ψ ≤ (C * D) • (η ∘ₘ σ) := by
  apply Measure.le_iff.mpr
  intro E hE
  rw [Measure.bind_apply hE κ.aemeasurable, Measure.smul_apply, smul_eq_mul,
    Measure.bind_apply hE η.aemeasurable]
  calc
    _ ≤ ∫⁻ s, D * η s E ∂ψ := lintegral_mono (fun s ↦ hrow s _)
    _ ≤ ∫⁻ s, D * η s E ∂(C • σ) := lintegral_mono' hprefix le_rfl
    _ = _ := by
      rw [lintegral_smul_measure, lintegral_const_mul _ (η.measurable_coe hE), mul_assoc]
      rfl

theorem sequenceSuccessLaw_le {V : ℕ → Type*} [∀ n, MeasurableSpace (V n)]
    (ν : (n : ℕ) → Measure (V n)) [∀ n, IsProbabilityMeasure (ν n)]
    (initial : S) {next : (n : ℕ) → S × V n → S} (hnext : ∀ n, Measurable (next n))
    {A : (n : ℕ) → Set (S × V n)} (hA : ∀ n, MeasurableSet (A n))
    (κ : ℕ → Kernel S S) (hstep : ∀ n s, sampledKernel (ν n) (hA n) (hnext n) s ≤
      (2 : ℝ≥0∞) • κ n s) (n : ℕ) :
    sequenceSuccessLaw ν initial next A n ≤
      (2 : ℝ≥0∞) ^ n • sequenceReferenceLaw κ initial n := by
  induction n with
  | zero => rw [sequenceSuccessLaw_zero]; simp [sequenceReferenceLaw]
  | succ n ih =>
      rw [sequenceSuccessLaw_succ ν initial hnext hA n, sequenceReferenceLaw, pow_succ]
      exact comp_le_mul_of_row_le _ _ _ _ _ _ ih (hstep n)

theorem sequenceSuccessLaw_univ_add_failure {V : ℕ → Type*} [∀ n, MeasurableSpace (V n)]
    (ν : (n : ℕ) → Measure (V n)) [∀ n, IsProbabilityMeasure (ν n)]
    (initial : S) {next : (n : ℕ) → S × V n → S} (hnext : ∀ n, Measurable (next n))
    {A : (n : ℕ) → Set (S × V n)} (hA : ∀ n, MeasurableSet (A n)) (n : ℕ) :
    sequenceSuccessLaw ν initial next A n univ +
      sequenceSampleLaw ν n (sequenceSuccess initial next A n)ᶜ = 1 := by
  rw [sequenceSuccessLaw, Measure.map_apply (measurable_sequenceState initial hnext n)
    MeasurableSet.univ, preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  exact (measure_add_measure_compl (measurableSet_sequenceSuccess initial hnext hA n)).trans
    measure_univ

theorem sequenceSuccessLaw_mass_step {V : ℕ → Type*} [∀ n, MeasurableSpace (V n)]
    (ν : (n : ℕ) → Measure (V n)) [∀ n, IsProbabilityMeasure (ν n)]
    (initial : S) {next : (n : ℕ) → S × V n → S} (hnext : ∀ n, Measurable (next n))
    {A : (n : ℕ) → Set (S × V n)} (hA : ∀ n, MeasurableSet (A n)) (n : ℕ) :
    sequenceSuccessLaw ν initial next A (n + 1) univ +
      (∫⁻ s, ν n {v | (s, v) ∉ A n} ∂sequenceSuccessLaw ν initial next A n) =
        sequenceSuccessLaw ν initial next A n univ := by
  rw [sequenceSuccessLaw_succ ν initial hnext hA,
    Measure.bind_apply MeasurableSet.univ (sampledKernel (ν n) (hA n) (hnext n)).aemeasurable,
    ← lintegral_add_left ((sampledKernel (ν n) (hA n) (hnext n)).measurable_coe MeasurableSet.univ)]
  simp_rw [sampledKernel_univ_add_failure (ν n) (hA n) (hnext n)]
  simp

theorem sequenceFailure_le_sum {V : ℕ → Type*} [∀ n, MeasurableSpace (V n)]
    (ν : (n : ℕ) → Measure (V n)) [∀ n, IsProbabilityMeasure (ν n)]
    (initial : S) {next : (n : ℕ) → S × V n → S} (hnext : ∀ n, Measurable (next n))
    {A : (n : ℕ) → Set (S × V n)} (hA : ∀ n, MeasurableSet (A n))
    (κ : ℕ → Kernel S S) (hstep : ∀ n s, sampledKernel (ν n) (hA n) (hnext n) s ≤
      (2 : ℝ≥0∞) • κ n s) (ε : ℕ → ℝ≥0∞)
    (hε : ∀ n, (∫⁻ s, ν n {v | (s, v) ∉ A n} ∂sequenceReferenceLaw κ initial n) ≤ ε n)
    (n : ℕ) :
    sequenceSampleLaw ν n (sequenceSuccess initial next A n)ᶜ ≤
      ∑ i ∈ Finset.range n, (2 : ℝ≥0∞) ^ i * ε i := by
  have hmass : ∀ n, 1 ≤ sequenceSuccessLaw ν initial next A n univ +
      ∑ i ∈ Finset.range n, (2 : ℝ≥0∞) ^ i * ε i := by
    intro n
    induction n with
    | zero => simp [sequenceSuccessLaw_zero]
    | succ n ih =>
        have hfail : (∫⁻ s, ν n {v | (s, v) ∉ A n} ∂sequenceSuccessLaw ν initial next A n) ≤
            (2 : ℝ≥0∞) ^ n * ε n := by
          calc
            _ ≤ ∫⁻ s, ν n {v | (s, v) ∉ A n}
                ∂((2 : ℝ≥0∞) ^ n • sequenceReferenceLaw κ initial n) :=
              lintegral_mono' (sequenceSuccessLaw_le ν initial hnext hA κ hstep n) le_rfl
            _ = (2 : ℝ≥0∞) ^ n *
                ∫⁻ s, ν n {v | (s, v) ∉ A n} ∂sequenceReferenceLaw κ initial n :=
              lintegral_smul_measure _ _
            _ ≤ _ := mul_le_mul_right (hε n) _
        calc
          _ ≤ sequenceSuccessLaw ν initial next A n univ +
              ∑ i ∈ Finset.range n, (2 : ℝ≥0∞) ^ i * ε i := ih
          _ = (sequenceSuccessLaw ν initial next A (n + 1) univ +
              ∫⁻ s, ν n {v | (s, v) ∉ A n} ∂sequenceSuccessLaw ν initial next A n) +
              ∑ i ∈ Finset.range n, (2 : ℝ≥0∞) ^ i * ε i := by
            rw [sequenceSuccessLaw_mass_step ν initial hnext hA n]
          _ ≤ (sequenceSuccessLaw ν initial next A (n + 1) univ + (2 : ℝ≥0∞) ^ n * ε n) +
              ∑ i ∈ Finset.range n, (2 : ℝ≥0∞) ^ i * ε i := by gcongr
          _ = _ := by rw [Finset.sum_range_succ]; ac_rfl
  apply ENNReal.le_of_add_le_add_left
    (measure_ne_top (sequenceSuccessLaw ν initial next A n) univ)
  rw [sequenceSuccessLaw_univ_add_failure ν initial hnext hA n]
  exact hmass n

end CapacityAtlas.MeasureBinning
