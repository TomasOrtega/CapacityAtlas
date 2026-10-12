/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.MeasureRandomBinning.RejectionSequence
import CapacityAtlasForMathlib.InformationTheory.MeasureRandomBinning.Packing

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical BigOperators

namespace CapacityAtlas.MeasureBinning

open MeasureChannel

def sequenceSampleAt {V : ℕ → Type*} : (n : ℕ) → SequenceSamples V n → (i : Fin n) → V i.val
  | 0, _, i => Fin.elim0 i
  | n + 1, samples, i => Fin.lastCases samples.2 (fun j ↦ sequenceSampleAt n samples.1 j) i

@[simp]
theorem sequenceSampleAt_last {V : ℕ → Type*} (n : ℕ) (samples : SequenceSamples V (n + 1)) :
    sequenceSampleAt (n + 1) samples (Fin.last n) = samples.2 := by
  simp [sequenceSampleAt]

@[simp]
theorem sequenceSampleAt_castSucc {V : ℕ → Type*} (n : ℕ)
    (samples : SequenceSamples V (n + 1)) (i : Fin n) :
    sequenceSampleAt (n + 1) samples i.castSucc = sequenceSampleAt n samples.1 i := by
  simp [sequenceSampleAt]

theorem measurable_sequenceSampleAt {V : ℕ → Type*} [∀ n, MeasurableSpace (V n)] :
    ∀ (n : ℕ) (i : Fin n), Measurable (fun samples : SequenceSamples V n ↦
      sequenceSampleAt n samples i)
  | 0, i => Fin.elim0 i
  | n + 1, i => by
      induction i using Fin.lastCases with
      | last =>
          simp only [sequenceSampleAt_last]
          change Measurable (Prod.snd : SequenceSamples V n × V n → V n)
          exact measurable_snd
      | cast j =>
          simp only [sequenceSampleAt_castSucc]
          change Measurable (fun p : SequenceSamples V n × V n ↦ sequenceSampleAt n p.1 j)
          exact (measurable_sequenceSampleAt n j).comp measurable_fst

def selectedRows {V M : ℕ → Type*} (message : (i : ℕ) → M i) :
    (n : ℕ) → SequenceSamples (fun i ↦ M i → V i) n → SequenceSamples V n
  | 0, _ => PUnit.unit
  | n + 1, books => (selectedRows message n books.1, books.2 (message n))

theorem sequenceSampleAt_selectedRows {V M : ℕ → Type*} (message : (i : ℕ) → M i)
    (n : ℕ) (books : SequenceSamples (fun i ↦ M i → V i) n) (i : Fin n) :
    sequenceSampleAt n (selectedRows message n books) i = sequenceSampleAt n books i (message i.val) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      induction i using Fin.lastCases with
      | last => simp only [sequenceSampleAt_last, selectedRows, Fin.val_last]
      | cast i =>
          simp only [sequenceSampleAt_castSucc, selectedRows, Fin.val_castSucc]
          exact ih books.1 i

theorem measurable_selectedRows {V M : ℕ → Type*} [∀ n, MeasurableSpace (V n)]
    (message : (i : ℕ) → M i) : ∀ n, Measurable (selectedRows (V := V) message n)
  | 0 => measurable_const
  | n + 1 => ((measurable_selectedRows message n).comp measurable_fst).prodMk
      ((measurable_pi_apply (message n)).comp measurable_snd)

theorem measurePreserving_selectedRows {V M : ℕ → Type*} [∀ n, MeasurableSpace (V n)]
    [∀ n, Fintype (M n)] (ν : (n : ℕ) → Measure (V n)) [∀ n, IsProbabilityMeasure (ν n)]
    (message : (i : ℕ) → M i) : ∀ n, MeasurePreserving (selectedRows (V := V) message n)
      (sequenceSampleLaw (fun i ↦ Measure.pi (fun _ : M i ↦ ν i)) n) (sequenceSampleLaw ν n)
  | 0 => ⟨measurable_const, Measure.map_dirac' measurable_const _⟩
  | n + 1 => (measurePreserving_selectedRows ν message n).prod
      (measurePreserving_eval (fun _ : M n ↦ ν n) (message n))

theorem lintegral_independent_row_acceptance {V Y M : Type*}
    [MeasurableSpace V] [MeasurableSpace Y] [Fintype M]
    (ν : Measure V) [IsProbabilityMeasure ν] (ρ : Kernel V Y) [IsMarkovKernel ρ]
    {A : Set (V × Y)} (hA : MeasurableSet A) {c : ℝ≥0∞}
    (huniform : ∀ y, ν {v | (v, y) ∈ A} ≤ c) {m j : M} (hmj : m ≠ j) :
    (∫⁻ book : M → V, ρ (book m) {y | (book j, y) ∈ A}
      ∂Measure.pi (fun _ : M ↦ ν)) ≤ c := by
  change (∫⁻ book : M → V, falseAcceptance ρ A (book m) (book j)
    ∂Measure.pi (fun _ : M ↦ ν)) ≤ c
  rw [lintegral_codebook_falseAcceptance ρ A hA ν hmj]
  apply le_trans (lintegral_mono (fun row ↦ lintegral_acceptance_le ν (ρ row) hA huniform))
  simp

theorem measurable_sequenceCompetingAcceptance {V M : ℕ → Type*} {Y : Type*}
    [∀ n, MeasurableSpace (V n)] [MeasurableSpace Y]
    (message : (i : ℕ) → M i) (n : ℕ) (i : Fin n) (j : M i.val)
    (ρ : Kernel (SequenceSamples V n) Y) [IsSFiniteKernel ρ]
    {A : Set (V i.val × Y)} (hA : MeasurableSet A) :
    Measurable (fun books : SequenceSamples (fun i ↦ M i → V i) n ↦
      ρ (selectedRows message n books) {y | (sequenceSampleAt n books i j, y) ∈ A}) := by
  let ρ' := ρ.comap (selectedRows message n) (measurable_selectedRows message n)
  have hm : Measurable (fun p : SequenceSamples (fun i ↦ M i → V i) n × Y ↦
      (sequenceSampleAt n p.1 i j, p.2)) :=
    ((measurable_pi_apply j).comp ((measurable_sequenceSampleAt n i).comp measurable_fst)).prodMk
      measurable_snd
  exact Kernel.measurable_kernel_prodMk_left (κ := ρ') (hA.preimage hm)

theorem lintegral_sequence_competingAcceptance_le {V M : ℕ → Type*} {Y : Type*}
    [∀ n, MeasurableSpace (V n)] [MeasurableSpace Y] [∀ n, Fintype (M n)]
    (ν : (n : ℕ) → Measure (V n)) [∀ n, IsProbabilityMeasure (ν n)]
    (message : (i : ℕ) → M i) (n : ℕ) (i : Fin n) (j : M i.val)
    (ρ : Kernel (SequenceSamples V n) Y) [IsMarkovKernel ρ]
    {A : Set (V i.val × Y)} (hA : MeasurableSet A) {c : ℝ≥0∞}
    (huniform : ∀ y, ν i.val {v | (v, y) ∈ A} ≤ c) (hne : message i.val ≠ j) :
    (∫⁻ books : SequenceSamples (fun i ↦ M i → V i) n,
      ρ (selectedRows message n books) {y | (sequenceSampleAt n books i j, y) ∈ A}
      ∂sequenceSampleLaw (fun i ↦ Measure.pi (fun _ : M i ↦ ν i)) n) ≤ c := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      induction i using Fin.lastCases with
      | last =>
          rw [sequenceSampleLaw]
          rw [lintegral_prod _ (measurable_sequenceCompetingAcceptance message (n + 1)
            (Fin.last n) j ρ hA).aemeasurable]
          apply le_trans (b := ∫⁻ _prior : SequenceSamples (fun i ↦ M i → V i) n, c
            ∂sequenceSampleLaw (fun i ↦ Measure.pi (fun _ : M i ↦ ν i)) n) ?_ (by simp)
          apply lintegral_mono
          intro prior
          let ρ' := ρ.comap (fun row : V n ↦ (selectedRows message n prior, row))
            (measurable_const.prodMk measurable_id)
          have hbound := lintegral_independent_row_acceptance (ν n) ρ' hA huniform hne
          simp only [ρ', Kernel.comap_apply, Fin.val_last] at hbound
          convert hbound using 1
          simp only [sequenceSampleAt_last, selectedRows]
          rfl
      | cast k =>
          rw [sequenceSampleLaw]
          rw [lintegral_prod_symm _ (measurable_sequenceCompetingAcceptance message (n + 1)
            k.castSucc j ρ hA).aemeasurable]
          apply le_trans (b := ∫⁻ _latest : M n → V n, c ∂Measure.pi (fun _ : M n ↦ ν n))
            ?_ (by simp)
          apply lintegral_mono
          intro latest
          let ρ' := ρ.comap (fun prior : SequenceSamples V n ↦ (prior, latest (message n)))
            (measurable_id.prodMk measurable_const)
          have hbound := ih k j ρ' hA huniform hne
          simp only [ρ', Kernel.comap_apply] at hbound
          convert hbound using 1
          simp only [sequenceSampleAt_castSucc, selectedRows]
          rfl

theorem lintegral_sequence_competingBins_le {V M : ℕ → Type*} {Y : Type*}
    [∀ n, MeasurableSpace (V n)] [MeasurableSpace Y] [∀ n, Fintype (M n)]
    (ν : (n : ℕ) → Measure (V n)) [∀ n, IsProbabilityMeasure (ν n)]
    (message : (i : ℕ) → M i) (n : ℕ) (i : Fin n)
    (ρ : Kernel (SequenceSamples V n) Y) [IsMarkovKernel ρ]
    {A : Set (V i.val × Y)} (hA : MeasurableSet A) {c : ℝ≥0∞}
    (huniform : ∀ y, ν i.val {v | (v, y) ∈ A} ≤ c) :
    (∫⁻ books : SequenceSamples (fun i ↦ M i → V i) n,
      ρ (selectedRows message n books)
        {y | ∃ j, j ≠ message i.val ∧ (sequenceSampleAt n books i j, y) ∈ A}
      ∂sequenceSampleLaw (fun i ↦ Measure.pi (fun _ : M i ↦ ν i)) n) ≤
        (Fintype.card (M i.val) - 1 : ℕ) * c := by
  have hpoint (books : SequenceSamples (fun i ↦ M i → V i) n) :
      ρ (selectedRows message n books)
          {y | ∃ j, j ≠ message i.val ∧ (sequenceSampleAt n books i j, y) ∈ A} ≤
        ∑ j ∈ Finset.univ.erase (message i.val),
          ρ (selectedRows message n books) {y | (sequenceSampleAt n books i j, y) ∈ A} := by
    have heq : {y | ∃ j, j ≠ message i.val ∧ (sequenceSampleAt n books i j, y) ∈ A} =
        ⋃ j ∈ Finset.univ.erase (message i.val), {y | (sequenceSampleAt n books i j, y) ∈ A} := by
      ext y
      simp
    rw [heq]
    exact measure_biUnion_finset_le _ _
  calc
    _ ≤ ∫⁻ books, ∑ j ∈ Finset.univ.erase (message i.val),
        ρ (selectedRows message n books) {y | (sequenceSampleAt n books i j, y) ∈ A}
        ∂sequenceSampleLaw (fun i ↦ Measure.pi (fun _ : M i ↦ ν i)) n := lintegral_mono hpoint
    _ = ∑ j ∈ Finset.univ.erase (message i.val), ∫⁻ books,
        ρ (selectedRows message n books) {y | (sequenceSampleAt n books i j, y) ∈ A}
        ∂sequenceSampleLaw (fun i ↦ Measure.pi (fun _ : M i ↦ ν i)) n :=
      lintegral_finsetSum _ (fun j _ ↦ measurable_sequenceCompetingAcceptance message n i j ρ hA)
    _ ≤ ∑ _j ∈ Finset.univ.erase (message i.val), c := by
      apply Finset.sum_le_sum
      intro j hj
      exact lintegral_sequence_competingAcceptance_le ν message n i j ρ hA huniform
        (Finset.mem_erase.mp hj).1.symm
    _ = _ := by simp [Finset.card_erase_of_mem]

def candidateRowAcceptance {U Y : Type*} (A : Set (U × Y)) (L : ℕ) :
    Set ((Fin L → U × ℝ) × Y) := {p | ∃ l, ((p.1 l).1, p.2) ∈ A}

theorem measurableSet_candidateRowAcceptance {U Y : Type*} [MeasurableSpace U]
    [MeasurableSpace Y] {A : Set (U × Y)} (hA : MeasurableSet A) (L : ℕ) :
    MeasurableSet (candidateRowAcceptance A L) := by
  simp only [candidateRowAcceptance, setOf_exists]
  exact MeasurableSet.iUnion (fun l ↦ hA.preimage
    (((measurable_pi_apply l).comp measurable_fst).fst.prodMk measurable_snd))

theorem candidateRowAcceptance_mass_le {U Y : Type*} [MeasurableSpace U]
    [MeasurableSpace Y] (μ : Measure U) [IsProbabilityMeasure μ]
    {A : Set (U × Y)} (hA : MeasurableSet A) {c : ℝ≥0∞}
    (huniform : ∀ y, μ {u | (u, y) ∈ A} ≤ c) (L : ℕ) (y : Y) :
    (Measure.pi (fun _ : Fin L ↦ μ.prod seedLaw))
      {row | (row, y) ∈ candidateRowAcceptance A L} ≤ (L : ℝ≥0∞) * c := by
  have heq : {row : Fin L → U × ℝ | (row, y) ∈ candidateRowAcceptance A L} =
      ⋃ l : Fin L, {row | ((row l).1, y) ∈ A} := by ext row; simp [candidateRowAcceptance]
  rw [heq]
  calc
    _ ≤ ∑ l : Fin L, (Measure.pi (fun _ : Fin L ↦ μ.prod seedLaw))
        {row | ((row l).1, y) ∈ A} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _l : Fin L, c := by
      apply Finset.sum_le_sum
      intro l _
      have hmp := (measurePreserving_fst (μ := μ) (ν := seedLaw)).comp
        (measurePreserving_eval (fun _ : Fin L ↦ μ.prod seedLaw) l)
      have hsection : MeasurableSet {u : U | (u, y) ∈ A} :=
        hA.preimage (measurable_id.prodMk measurable_const)
      exact (hmp.measure_preimage hsection.nullMeasurableSet).le.trans (huniform y)
    _ = _ := by simp

end CapacityAtlas.MeasureBinning
