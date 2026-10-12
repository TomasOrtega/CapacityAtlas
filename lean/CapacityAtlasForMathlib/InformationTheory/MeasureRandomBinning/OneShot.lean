/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.MeasureRandomBinning.Ensemble

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical

namespace CapacityAtlas.MeasureBinning

variable {S U X Y M L : Type*} [MeasurableSpace S] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace M]
  [Fintype M] [Nonempty M] [Fintype L] [Nonempty L]

noncomputable def binningKernel (κ : Kernel (S × X) Y)
    (B : Set (S × U)) (hB : MeasurableSet B) (input : S × U → X)
    (hinput : Measurable input) (fallback : S → X) (hfallback : Measurable fallback) :
    Kernel ((L → U) × S) Y :=
  κ.comap (fun p ↦ (p.2, binningInput B input fallback p.1 p.2))
    (measurable_snd.prodMk (measurable_binningInput hB hinput hfallback))

instance (κ : Kernel (S × X) Y) [IsMarkovKernel κ]
    (B : Set (S × U)) (hB : MeasurableSet B) (input : S × U → X)
    (hinput : Measurable input) (fallback : S → X) (hfallback : Measurable fallback) :
    IsMarkovKernel (binningKernel (L := L) κ B hB input hinput fallback hfallback) := by
  unfold binningKernel
  infer_instance

theorem stateAverageError_binningCode_le
    (κ : Kernel (S × X) Y) [IsMarkovKernel κ] (σ : Measure S)
    (B : Set (S × U)) (hB : MeasurableSet B) (input : S × U → X)
    (hinput : Measurable input) (fallback : S → X) (hfallback : Measurable fallback)
    (A : Set (U × Y)) (hA : MeasurableSet A) {δ : ℝ≥0∞}
    (hmiss : ∀ z ∈ B, κ (z.1, input z) {y | (z.2, y) ∉ A} ≤ δ)
    (book : M → L → U) :
    stateAverageError κ σ (binningCode B hB input hinput fallback hfallback A hA book) ≤
      binningBound (binningKernel κ B hB input hinput fallback hfallback) σ δ B A book := by
  unfold stateAverageError binningBound
  gcongr with m
  apply lintegral_mono
  intro s
  exact binningCode_conditionalError_le κ B hB input hinput fallback hfallback A hA hmiss book m s

/-- Finite random binning yields a deterministic measurable state-dependent code. -/
theorem exists_stateCode_error_le
    (κ : Kernel (S × X) Y) [IsMarkovKernel κ]
    (σ : Measure S) [IsProbabilityMeasure σ]
    (η : Kernel S U) [IsMarkovKernel η] (μ : Measure U) [IsProbabilityMeasure μ]
    (g : S × U → ℝ≥0∞)
    (hrow : ∀ s, η s = μ.withDensity (fun u ↦ g (s, u)))
    (B : Set (S × U)) (hB : MeasurableSet B) {T : ℝ} (hT : 0 < T)
    (hcut : ∀ z ∈ B, g z ≤ ENNReal.ofReal T)
    (input : S × U → X) (hinput : Measurable input) (fallback : S → X)
    (hfallback : Measurable fallback) (A : Set (U × Y)) (hA : MeasurableSet A)
    {δ c : ℝ≥0∞} (hmiss : ∀ z ∈ B, κ (z.1, input z) {y | (z.2, y) ∉ A} ≤ δ)
    (hAuniform : ∀ y, μ {u | (u, y) ∈ A} ≤ c)
    (allowed : Set (S × X)) (hgood : ∀ z ∈ B, (z.1, input z) ∈ allowed)
    (hfallback_mem : ∀ s, (s, fallback s) ∈ allowed) :
    ∃ code : StateCode S X Y M, (∀ m s, (s, code.encode m s) ∈ allowed) ∧
      stateAverageError κ σ code ≤
        2 * (σ ⊗ₘ η) Bᶜ +
          ENNReal.ofReal (Real.exp (-((Fintype.card L : ℝ) * ((1 / 2) / T)))) + δ +
          (Fintype.card M - 1 : ℕ) * Fintype.card L * c := by
  let ρ := binningKernel (L := L) κ B hB input hinput fallback hfallback
  obtain ⟨book, hbook⟩ := exists_le_lintegral
    (μ := Measure.pi (fun _ : M ↦ Measure.pi (fun _ : L ↦ μ)))
    (measurable_binningBound ρ σ δ hB hA).aemeasurable
  refine ⟨binningCode B hB input hinput fallback hfallback A hA book,
    fun m s ↦ binningCode_mem_allowed B hB input hinput fallback hfallback A hA allowed
      hgood hfallback_mem book m s, ?_⟩
  apply (stateAverageError_binningCode_le κ σ B hB input hinput fallback hfallback A hA
    hmiss book).trans
  apply hbook.trans
  apply (lintegral_binningBound_le σ μ ρ δ hB hA hAuniform).trans
  exact add_le_add (add_le_add (lintegral_coveringFailure_le σ η μ g hrow hB hT hcut)
    le_rfl) le_rfl

end CapacityAtlas.MeasureBinning
