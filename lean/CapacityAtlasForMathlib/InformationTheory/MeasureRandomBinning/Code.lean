/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.MeasureRandomBinning.Covering

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical

namespace CapacityAtlas.MeasureBinning

open MeasureChannel

structure StateCode (S X Y M : Type*) [MeasurableSpace S] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace M] where
  encode : M → S → X
  measurable_encode : ∀ m, Measurable (encode m)
  decode : Y → M
  measurable_decode : Measurable decode

variable {S U X Y M L : Type*} [MeasurableSpace S] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace M]

noncomputable def stateErrorProbability (κ : Kernel (S × X) Y) (σ : Measure S)
    (code : StateCode S X Y M) (m : M) : ℝ≥0∞ :=
  ∫⁻ s, κ (s, code.encode m s) {y | code.decode y ≠ m} ∂σ

noncomputable def stateAverageError [Fintype M] (κ : Kernel (S × X) Y) (σ : Measure S)
    (code : StateCode S X Y M) : ℝ≥0∞ :=
  (Fintype.card M : ℝ≥0∞)⁻¹ * ∑ m, stateErrorProbability κ σ code m

variable [Fintype L] [Nonempty L]

noncomputable def binningInput (B : Set (S × U)) (input : S × U → X) (fallback : S → X)
    (book : L → U) (s : S) : X :=
  if coveringFailure B book s then fallback s else input (s, selectAux B book s)

theorem measurable_binningInput {B : Set (S × U)} (hB : MeasurableSet B)
    {input : S × U → X} (hinput : Measurable input) {fallback : S → X}
    (hfallback : Measurable fallback) :
    Measurable (fun p : (L → U) × S ↦ binningInput B input fallback p.1 p.2) := by
  exact Measurable.ite (measurableSet_coveringFailure hB) (hfallback.comp measurable_snd)
    (hinput.comp (measurable_snd.prodMk (measurable_selectAux hB)))

omit [MeasurableSpace S] [MeasurableSpace U] [MeasurableSpace X] in
theorem binningInput_mem_allowed (B : Set (S × U)) (input : S × U → X) (fallback : S → X)
    (allowed : Set (S × X)) (hgood : ∀ z ∈ B, (z.1, input z) ∈ allowed)
    (hfallback : ∀ s, (s, fallback s) ∈ allowed) (book : L → U) (s : S) :
    (s, binningInput B input fallback book s) ∈ allowed := by
  unfold binningInput
  split_ifs with hfail
  · exact hfallback s
  · exact hgood _ (selectAux_mem B hfail)

variable [Fintype M] [Nonempty M]

noncomputable def binningDecoder (A : Set (U × Y)) (book : M → L → U) (y : Y) : M :=
  (firstAccepted (fun p y ↦ (book p.1 p.2, y) ∈ A)
    (Classical.choice inferInstance : M × L) Finset.univ.toList y).1

theorem measurable_binningDecoder {A : Set (U × Y)} (hA : MeasurableSet A)
    (book : M → L → U) : Measurable (binningDecoder A book) := by
  letI : MeasurableSpace L := ⊤
  exact measurable_fst.comp (measurable_firstAccepted _ _
    (fun p ↦ hA.preimage (measurable_const.prodMk measurable_id)) _)

omit [MeasurableSpace U] [MeasurableSpace Y] [MeasurableSpace M] in
theorem binningDecoder_eq_of_accepts (A : Set (U × Y)) (book : M → L → U)
    (m : M) (y : Y) (hhit : ∃ l, (book m l, y) ∈ A)
    (hother : ∀ j, j ≠ m → ∀ l, (book j l, y) ∉ A) : binningDecoder A book y = m := by
  have hacc : (book (firstAccepted (fun p y ↦ (book p.1 p.2, y) ∈ A)
      (Classical.choice inferInstance : M × L) Finset.univ.toList y).1
      (firstAccepted (fun p y ↦ (book p.1 p.2, y) ∈ A)
      (Classical.choice inferInstance : M × L) Finset.univ.toList y).2, y) ∈ A := by
    apply firstAccepted_accepts (fun (p : M × L) y ↦ (book p.1 p.2, y) ∈ A)
    obtain ⟨l, hl⟩ := hhit
    exact ⟨(m, l), by simp, hl⟩
  by_contra hne
  exact hother _ hne _ hacc

noncomputable def binningCode (B : Set (S × U)) (hB : MeasurableSet B)
    (input : S × U → X) (hinput : Measurable input) (fallback : S → X)
    (hfallback : Measurable fallback) (A : Set (U × Y)) (hA : MeasurableSet A)
    (book : M → L → U) : StateCode S X Y M where
  encode m := binningInput B input fallback (book m)
  measurable_encode _ := (measurable_binningInput hB hinput hfallback).comp
    (measurable_const.prodMk measurable_id)
  decode := binningDecoder A book
  measurable_decode := measurable_binningDecoder hA book

theorem binningCode_mem_allowed (B : Set (S × U)) (hB : MeasurableSet B)
    (input : S × U → X) (hinput : Measurable input) (fallback : S → X)
    (hfallback : Measurable fallback) (A : Set (U × Y)) (hA : MeasurableSet A)
    (allowed : Set (S × X)) (hgood : ∀ z ∈ B, (z.1, input z) ∈ allowed)
    (hfallback_mem : ∀ s, (s, fallback s) ∈ allowed) (book : M → L → U) (m : M) (s : S) :
    (s, (binningCode B hB input hinput fallback hfallback A hA book).encode m s) ∈ allowed :=
  binningInput_mem_allowed B input fallback allowed hgood hfallback_mem (book m) s

omit [MeasurableSpace U] [MeasurableSpace M] in
theorem binningDecoder_error_le (ν : Measure Y) (A : Set (U × Y))
    (book : M → L → U) (m : M) (l : L) :
    ν {y | binningDecoder A book y ≠ m} ≤
      ν {y | (book m l, y) ∉ A} +
        ∑ j ∈ Finset.univ.erase m, ∑ k : L, ν {y | (book j k, y) ∈ A} := by
  have hsubset : {y | binningDecoder A book y ≠ m} ⊆
      {y | (book m l, y) ∉ A} ∪
        ⋃ j ∈ Finset.univ.erase m, ⋃ k : L, {y | (book j k, y) ∈ A} := by
    intro y hy
    by_cases hhit : (book m l, y) ∈ A
    · right
      by_contra hnone
      apply hy
      apply binningDecoder_eq_of_accepts A book m y ⟨l, hhit⟩
      intro j hj k hk
      apply hnone
      exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr
        ⟨Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩, Set.mem_iUnion.mpr ⟨k, hk⟩⟩⟩
    · exact Or.inl hhit
  apply (measure_mono hsubset).trans
  apply (measure_union_le _ _).trans
  apply add_le_add le_rfl
  exact (measure_biUnion_finset_le _ _).trans
    (Finset.sum_le_sum (fun j _ ↦ measure_iUnion_fintype_le _ _))

theorem binningCode_conditionalError_le (κ : Kernel (S × X) Y) [IsMarkovKernel κ]
    (B : Set (S × U)) (hB : MeasurableSet B) (input : S × U → X)
    (hinput : Measurable input) (fallback : S → X) (hfallback : Measurable fallback)
    (A : Set (U × Y)) (hA : MeasurableSet A) {δ : ℝ≥0∞}
    (hmiss : ∀ z ∈ B, κ (z.1, input z) {y | (z.2, y) ∉ A} ≤ δ)
    (book : M → L → U) (m : M) (s : S) :
    κ (s, (binningCode B hB input hinput fallback hfallback A hA book).encode m s)
        {y | binningDecoder A book y ≠ m} ≤
      (if coveringFailure B (book m) s then 1 else 0) + δ +
        ∑ j ∈ Finset.univ.erase m, ∑ k : L,
          κ (s, (binningCode B hB input hinput fallback hfallback A hA book).encode m s)
            {y | (book j k, y) ∈ A} := by
  by_cases hfail : coveringFailure B (book m) s
  · simp only [if_pos hfail]
    exact prob_le_one.trans ((le_add_right le_rfl).trans (le_add_right le_rfl))
  · simp only [if_neg hfail, zero_add]
    apply (binningDecoder_error_le _ A book m (selectIndex B (book m) s)).trans
    apply add_le_add _ le_rfl
    simpa only [binningCode, binningInput, if_neg hfail, selectAux] using
      hmiss (s, selectAux B (book m) s) (selectAux_mem B hfail)

end CapacityAtlas.MeasureBinning
